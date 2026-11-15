// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Spellings of a type name the file declares, and of a ghost scalar name,
//! that need not denote the type the lane reads them as.
//!
//! The lane reads a type the file declares (a `struct`, `enum`, `union` or
//! `type` item) by its name: the source type registry keys each declaration
//! by its bare name, whatever inline module holds it, and reads a path by the
//! segment that names a declaration. Rust resolves each spelling in its own
//! scope instead. So beside `mod a { pub type W = u64; }`, the `W` of `use
//! c::V as W;`, of `use other::W;` and of `type V = other::W;` is not `a::W`,
//! and the lane reads it as `a::W`. [`declared_name_hazard`] finds
//!
//! * a `use` that binds a declared name and does not import a declaration
//!   or a `use` of that same name from a module of the file: a rename
//!   (`use c::V as W;`), or a path the file does not show (`use other::W;`,
//!   `use crate::m::W;`, `use other_crate::W;`);
//! * a path whose segment after the first is a declared name, where the
//!   segments before it do not lead to a module of the file that declares or
//!   imports that name, or to an enum with a variant of that name (`other::W`,
//!   `crate::a::W`, `<T as Tr>::W`), in the syntax tree and in the tokens of
//!   macros and attributes; and `Self::W` where `Self` need not be an enum
//!   with a variant `W` (see `self_paths`: in a trait, `Self::Item` can be an
//!   associated type of a supertrait the file does not declare).
//!
//! [`ghost_scalar_import_hazard`] finds a `use` that binds `int`, `nat` or
//! `real` other than from this toolchain's crates, directly or through `use`
//! items of inline modules of the file (`use super::int;` under `use
//! trust_vc_types::int;`). The lane reads those names as mathematical types
//! wherever they are spelled, and an import from elsewhere can make them
//! anything (`pub type int = u8;`).

use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::{TokenStream, TokenTree};
use syn::visit::Visit;
use syn::{File, ItemFn};

use super::self_paths::{self_path_not_variant, SelfVariants};
use super::{is_ghost_scalar, is_path_sep, path_segments, resolve_in_frames, unraw, Frame, Target};

/// The crate roots of this toolchain, whose `int`, `nat` and `real` are the
/// ones the lane reads.
pub(super) const TOOLCHAIN_ROOTS: &[&str] = &["trust_vc", "trust_vc_types", "trust_mc", "vstd"];

/// The first name of [`TOOLCHAIN_ROOTS`] that `file` or `func` binds, in the
/// type namespace, to something other than the crate of that name,
/// described: an item of that name (`mod vstd;`, `mod trust_vc_types { .. }`),
/// a `use` that binds it from another path (`use other as vstd;`, `use
/// crate::m::vstd;`), or an `extern crate` of another crate under it
/// (`extern crate other_crate as trust_vc_types;`). A path's first segment
/// resolves in the scope it is written in before the extern prelude, so under
/// such a binding `use vstd::int;` need not import the toolchain's `int`. The
/// binding counts at any depth: in a crate built with the 2015 edition, `use
/// vstd::int;` in any module starts at the crate root.
pub(in crate::vc_extraction) fn rebound_toolchain_root(
    file: Option<&File>,
    func: &ItemFn,
) -> Option<String> {
    fn walk(tree: &syn::UseTree, prefix: &mut Vec<String>, found: &mut Option<String>) {
        let (leaf, bound) = match tree {
            syn::UseTree::Path(path) => {
                prefix.push(unraw(&path.ident));
                walk(&path.tree, prefix, found);
                prefix.pop();
                return;
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    walk(item, prefix, found);
                }
                return;
            }
            syn::UseTree::Glob(_) => return,
            syn::UseTree::Name(name) => {
                let leaf = unraw(&name.ident);
                let bound = if leaf == "self" {
                    prefix.last().cloned()
                } else {
                    Some(leaf.clone())
                };
                (leaf, bound)
            }
            syn::UseTree::Rename(rename) => (unraw(&rename.ident), Some(unraw(&rename.rename))),
        };
        let Some(bound) = bound else {
            return;
        };
        // `use vstd;`, `use vstd as vstd;` and `use vstd::{self};` import the
        // crate itself.
        let the_crate = (prefix.is_empty() && leaf == bound)
            || (leaf == "self" && prefix.as_slice() == [bound.clone()]);
        if found.is_none() && !the_crate && TOOLCHAIN_ROOTS.contains(&bound.as_str()) {
            let mut path = prefix.clone();
            path.push(leaf.clone());
            let rename = if leaf == bound || leaf == "self" {
                String::new()
            } else {
                format!(" as {bound}")
            };
            *found = Some(format!(
                "`{bound}`, the name of a crate of this toolchain, with `use {}{rename};`",
                path.join("::")
            ));
        }
    }
    #[derive(Default)]
    struct Find(Option<String>);
    impl<'ast> Visit<'ast> for Find {
        fn visit_item(&mut self, item: &'ast syn::Item) {
            let declared = match item {
                syn::Item::Mod(it) => Some(("mod", &it.ident)),
                syn::Item::Struct(it) => Some(("struct", &it.ident)),
                syn::Item::Enum(it) => Some(("enum", &it.ident)),
                syn::Item::Union(it) => Some(("union", &it.ident)),
                syn::Item::Type(it) => Some(("type", &it.ident)),
                syn::Item::Trait(it) => Some(("trait", &it.ident)),
                syn::Item::TraitAlias(it) => Some(("trait", &it.ident)),
                _ => None,
            };
            if let Some((keyword, ident)) = declared {
                let name = unraw(ident);
                if self.0.is_none() && TOOLCHAIN_ROOTS.contains(&name.as_str()) {
                    self.0 = Some(format!(
                        "`{name}`, the name of a crate of this toolchain, with `{keyword} {name}`"
                    ));
                }
            }
            match item {
                syn::Item::Use(it) => walk(&it.tree, &mut Vec::new(), &mut self.0),
                syn::Item::ExternCrate(it) => {
                    if let Some((_, rename)) = &it.rename {
                        let bound = unraw(rename);
                        let source = unraw(&it.ident);
                        if self.0.is_none()
                            && TOOLCHAIN_ROOTS.contains(&bound.as_str())
                            && source != bound
                        {
                            self.0 = Some(format!(
                                "`{bound}`, the name of a crate of this toolchain, with `extern \
                                 crate {source} as {bound};`"
                            ));
                        }
                    }
                }
                _ => {}
            }
            syn::visit::visit_item(self, item);
        }
    }
    let mut find = Find::default();
    if let Some(file) = file {
        find.visit_file(file);
    }
    find.visit_item_fn(func);
    find.0
}

/// Every name a `struct`, `enum`, `union` or `type` item declares anywhere in
/// `file` (in modules, bodies and blocks), and in `func`.
pub(super) fn declared_type_names(file: Option<&File>, func: &ItemFn) -> BTreeSet<String> {
    #[derive(Default)]
    struct Collect(BTreeSet<String>);
    impl<'ast> Visit<'ast> for Collect {
        fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
            self.0.insert(unraw(&item.ident));
            syn::visit::visit_item_struct(self, item);
        }
        fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
            self.0.insert(unraw(&item.ident));
            syn::visit::visit_item_enum(self, item);
        }
        fn visit_item_union(&mut self, item: &'ast syn::ItemUnion) {
            self.0.insert(unraw(&item.ident));
            syn::visit::visit_item_union(self, item);
        }
        fn visit_item_type(&mut self, item: &'ast syn::ItemType) {
            self.0.insert(unraw(&item.ident));
            syn::visit::visit_item_type(self, item);
        }
    }
    let mut collect = Collect::default();
    if let Some(file) = file {
        collect.visit_file(file);
    }
    collect.visit_item_fn(func);
    collect.0
}

/// Whether `func` is a copy of a function the file holds: a free function, a
/// method or a trait default with the same name and body. Such a copy is read
/// in its place in the file, with the scopes around it.
pub(super) fn file_holds(file: &File, func: &ItemFn) -> bool {
    struct Find<'a> {
        name: &'a syn::Ident,
        body: String,
        found: bool,
    }
    impl<'ast> Visit<'ast> for Find<'_> {
        fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
            if item.sig.ident == *self.name
                && quote::ToTokens::to_token_stream(&item.block).to_string() == self.body
            {
                self.found = true;
            }
            syn::visit::visit_item_fn(self, item);
        }
        fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
            if item.sig.ident == *self.name
                && quote::ToTokens::to_token_stream(&item.block).to_string() == self.body
            {
                self.found = true;
            }
            syn::visit::visit_impl_item_fn(self, item);
        }
        fn visit_trait_item_fn(&mut self, item: &'ast syn::TraitItemFn) {
            if item.sig.ident == *self.name
                && item.default.as_ref().is_some_and(|block| {
                    quote::ToTokens::to_token_stream(block).to_string() == self.body
                })
            {
                self.found = true;
            }
            syn::visit::visit_trait_item_fn(self, item);
        }
    }
    let mut find = Find {
        name: &func.sig.ident,
        body: quote::ToTokens::to_token_stream(&func.block).to_string(),
        found: false,
    };
    find.visit_file(file);
    find.found
}

/// The first spelling in `file` and `func` of a name in `declared` that need
/// not denote the file's declaration of it (see the module documentation),
/// described. `variants` holds the file's enums and associated types, which
/// decide where a path names a variant.
pub(super) fn declared_name_hazard(
    file: Option<&File>,
    func: &ItemFn,
    declared: &BTreeSet<String>,
    variants: &SelfVariants<'_>,
) -> Option<String> {
    if declared.is_empty() {
        return None;
    }
    let mut scan = DeclaredNameScan {
        frames: Vec::new(),
        declared,
        variants,
        hazard: None,
    };
    match file {
        Some(file) => {
            scan.frames.push(Frame::Module(&file.items));
            scan.visit_file(file);
            // A function the file does not hold (a transformed copy) is read
            // at file scope.
            if scan.hazard.is_none() && !file_holds(file, func) {
                scan.visit_item_fn(func);
            }
        }
        None => scan.visit_item_fn(func),
    }
    scan.hazard.or_else(|| {
        self_path_not_variant(file, Some(func), variants, &|name| declared.contains(name)).map(
            |name| {
                format!(
                    "the path `Self :: {name}` spells `{name}`, a type name this file declares, \
                     where `Self` need not be an enum with a variant `{name}`"
                )
            },
        )
    })
}

/// Walks a file with the scopes around each `use` and path.
struct DeclaredNameScan<'a, 'ast> {
    /// The enclosing scopes, outermost first.
    frames: Vec<Frame<'ast>>,
    declared: &'a BTreeSet<String>,
    variants: &'a SelfVariants<'a>,
    hazard: Option<String>,
}

impl DeclaredNameScan<'_, '_> {
    fn found(&mut self, hazard: String) {
        if self.hazard.is_none() {
            self.hazard = Some(hazard);
        }
    }

    /// Whether `name`, spelled after `prefix` in the innermost frame, names a
    /// declaration or an import of `name` in a module of the file, or a
    /// variant of an enum. `Self::name` is left to `self_paths`, which knows
    /// what `Self` is where the path is written.
    fn qualified_spelling_is_read(
        &self,
        leading_colon: bool,
        prefix: &[String],
        name: &str,
    ) -> bool {
        if prefix.last().is_some_and(|owner| owner == "Self") {
            return prefix.len() == 1;
        }
        match resolve_in_frames(&self.frames, leading_colon, prefix) {
            Some(Target::Module(items)) => items.iter().any(|item| declares_or_imports(item, name)),
            // `E::W` is a variant only where no associated type `W` is
            // declared: `impl E { type W = u8; }` makes it that type.
            Some(Target::Enum) => {
                !self.variants.associated.contains(name)
                    && self
                        .variants
                        .enums
                        .values()
                        .any(|variants| variants.contains(name))
            }
            None => false,
        }
    }

    /// Checks each segment after the first of a path written in the syntax
    /// tree.
    fn check_path(&mut self, path: &syn::Path) {
        let leading_colon = path.leading_colon.is_some();
        let mut prefix = Vec::new();
        for (index, segment) in path.segments.iter().enumerate() {
            let name = unraw(&segment.ident);
            if index > 0 && self.declared.contains(&name) {
                let read = path
                    .segments
                    .iter()
                    .take(index)
                    .all(|segment| segment.arguments.is_none())
                    && self.qualified_spelling_is_read(leading_colon, &prefix, &name);
                if !read {
                    let written = quote::ToTokens::to_token_stream(path).to_string();
                    self.found(format!(
                        "the path `{written}` spells `{name}`, a type name this file declares, \
                         after segments that do not lead to that declaration in this file"
                    ));
                }
            }
            prefix.push(name);
        }
    }

    /// Checks each path in the tokens of a macro or an attribute.
    fn check_tokens(&mut self, tokens: TokenStream) {
        let flat: Vec<TokenTree> = tokens.into_iter().collect();
        for (index, tree) in flat.iter().enumerate() {
            match tree {
                TokenTree::Group(group) => self.check_tokens(group.stream()),
                TokenTree::Ident(ident) => {
                    let name = unraw(ident);
                    if !self.declared.contains(&name)
                        || index < 2
                        || !is_path_sep(&flat[index - 2], &flat[index - 1])
                    {
                        continue;
                    }
                    let before = &flat[..index];
                    let read = path_segments(before).is_some_and(|prefix| {
                        let start = before.len() - 3 * prefix.len();
                        let leading_colon =
                            start >= 2 && is_path_sep(&before[start - 2], &before[start - 1]);
                        !prefix.is_empty()
                            && self.qualified_spelling_is_read(leading_colon, &prefix, &name)
                    });
                    if !read {
                        self.found(format!(
                            "a path in the tokens of a macro or an attribute spells `{name}`, a \
                             type name this file declares, after segments that do not lead to \
                             that declaration in this file"
                        ));
                    }
                }
                _ => {}
            }
        }
    }
}

impl<'ast> Visit<'ast> for DeclaredNameScan<'_, 'ast> {
    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        if let Some((_, items)) = &item.content {
            self.frames.push(Frame::Module(items));
            syn::visit::visit_item_mod(self, item);
            self.frames.pop();
        } else {
            syn::visit::visit_item_mod(self, item);
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
        use_bindings(&item.tree, &mut Vec::new(), &mut bindings);
        for UseBinding {
            prefix,
            leaf,
            bound,
        } in bindings
        {
            if !self.declared.contains(&bound) {
                continue;
            }
            let rendered = format!(
                "{}{}",
                if leading_colon { "::" } else { "" },
                prefix
                    .iter()
                    .chain(std::iter::once(&leaf))
                    .cloned()
                    .collect::<Vec<_>>()
                    .join("::")
            );
            if leaf != bound {
                self.found(format!(
                    "the `use` of `{rendered}` binds `{bound}`, a type name this file \
                     declares, to an item of another name"
                ));
            } else if !self.qualified_spelling_is_read(leading_colon, &prefix, &bound) {
                self.found(format!(
                    "the `use` of `{rendered}` binds `{bound}`, a type name this file \
                     declares, from a path that does not lead to that declaration in this file"
                ));
            }
        }
        syn::visit::visit_item_use(self, item);
    }

    fn visit_path(&mut self, path: &'ast syn::Path) {
        self.check_path(path);
        syn::visit::visit_path(self, path);
    }

    fn visit_type_path(&mut self, path: &'ast syn::TypePath) {
        if let Some(qself) = &path.qself {
            self.check_qualified_self(qself, &path.path);
        }
        syn::visit::visit_type_path(self, path);
    }

    fn visit_expr_path(&mut self, path: &'ast syn::ExprPath) {
        if let Some(qself) = &path.qself {
            self.check_qualified_self(qself, &path.path);
        }
        syn::visit::visit_expr_path(self, path);
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

impl DeclaredNameScan<'_, '_> {
    /// `<T>::W` and `<T as Tr>::W` name an associated item of `T`; one spelled
    /// like a declared type need not be that type.
    fn check_qualified_self(&mut self, qself: &syn::QSelf, path: &syn::Path) {
        for segment in path.segments.iter().skip(qself.position) {
            let name = unraw(&segment.ident);
            if self.declared.contains(&name) {
                self.found(format!(
                    "a qualified path names an associated item `{name}`, a type name this file \
                     declares"
                ));
            }
        }
    }
}

/// Whether `item` is a declaration of the type `name` or a non-glob `use`
/// that binds `name`.
fn declares_or_imports(item: &syn::Item, name: &str) -> bool {
    let ident = match item {
        syn::Item::Struct(it) => &it.ident,
        syn::Item::Enum(it) => &it.ident,
        syn::Item::Union(it) => &it.ident,
        syn::Item::Type(it) => &it.ident,
        syn::Item::Use(it) => return super::use_binds(&it.tree, name),
        _ => return false,
    };
    unraw(ident) == name
}

/// One name a `use` tree binds without a glob.
pub(super) struct UseBinding {
    /// The path above the imported item, from the root.
    pub(super) prefix: Vec<String>,
    /// The imported item's name as the path spells it.
    pub(super) leaf: String,
    /// The name the `use` binds (the rename, if any).
    pub(super) bound: String,
}

/// Every name `tree` binds without a glob, except a module bound by a `self`
/// leaf and a `_` rename.
pub(super) fn use_bindings(
    tree: &syn::UseTree,
    prefix: &mut Vec<String>,
    out: &mut Vec<UseBinding>,
) {
    match tree {
        syn::UseTree::Path(path) => {
            prefix.push(unraw(&path.ident));
            use_bindings(&path.tree, prefix, out);
            prefix.pop();
        }
        syn::UseTree::Group(group) => {
            for item in &group.items {
                use_bindings(item, prefix, out);
            }
        }
        syn::UseTree::Name(leaf) if leaf.ident != "self" => {
            let name = unraw(&leaf.ident);
            out.push(UseBinding {
                prefix: prefix.clone(),
                leaf: name.clone(),
                bound: name,
            });
        }
        syn::UseTree::Rename(rename) if rename.ident != "self" && rename.rename != "_" => {
            out.push(UseBinding {
                prefix: prefix.clone(),
                leaf: unraw(&rename.ident),
                bound: unraw(&rename.rename),
            });
        }
        syn::UseTree::Name(_) | syn::UseTree::Rename(_) | syn::UseTree::Glob(_) => {}
    }
}

/// A `use` that binds a ghost scalar name.
struct GhostImport {
    /// The path as written after `use`.
    rendered: String,
    /// The module whose items hold the `use` (by the address of its item
    /// list), or `None` for a `use` in a block, which no path can reach.
    owner: Option<usize>,
    /// The name it binds.
    name: String,
    /// Imported from a crate of this toolchain.
    toolchain: bool,
    /// The module of the file its path leads to, by the address of its item
    /// list, when it imports from one.
    target: Option<usize>,
}

/// A `use` that binds `int`, `nat` or `real` other than from this toolchain's
/// crates, directly or through `use` items of inline modules of the file,
/// rendered. A `use` that renames another name to one of them is the type-name
/// rule's (see `Scan::use_tree`).
pub(super) fn ghost_scalar_import_hazard(file: Option<&File>, func: &ItemFn) -> Option<String> {
    #[derive(Default)]
    struct Collect<'ast> {
        frames: Vec<Frame<'ast>>,
        imports: Vec<GhostImport>,
    }
    impl<'ast> Visit<'ast> for Collect<'ast> {
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
            use_bindings(&item.tree, &mut Vec::new(), &mut bindings);
            let owner = match self.frames.last() {
                Some(Frame::Module(items)) => Some(items.as_ptr() as usize),
                _ => None,
            };
            for UseBinding {
                prefix,
                leaf,
                bound,
            } in bindings
            {
                if !is_ghost_scalar(&bound) || leaf != bound {
                    continue;
                }
                let toolchain = prefix
                    .first()
                    .is_some_and(|root| TOOLCHAIN_ROOTS.contains(&root.as_str()));
                let target = match resolve_in_frames(&self.frames, leading_colon, &prefix) {
                    Some(Target::Module(items)) => Some(items.as_ptr() as usize),
                    _ => None,
                };
                self.imports.push(GhostImport {
                    rendered: format!(
                        "{}{}::{leaf}",
                        if leading_colon { "::" } else { "" },
                        prefix.join("::")
                    ),
                    owner,
                    name: bound,
                    toolchain,
                    target,
                });
            }
        }
    }
    let mut collect = Collect::default();
    match file {
        Some(file) => {
            collect.frames.push(Frame::Module(&file.items));
            collect.visit_file(file);
            if !file_holds(file, func) {
                collect.visit_item_fn(func);
            }
        }
        None => collect.visit_item_fn(func),
    }
    let imports = collect.imports;
    // A module binds a name to the toolchain's scalar when one of its own
    // `use` items imports it from the toolchain, or from a module that does.
    let mut good: Vec<bool> = imports.iter().map(|import| import.toolchain).collect();
    loop {
        let bound: BTreeMap<(usize, &str), ()> = imports
            .iter()
            .zip(&good)
            .filter_map(|(import, good)| {
                (*good)
                    .then_some(
                        import
                            .owner
                            .map(|owner| ((owner, import.name.as_str()), ())),
                    )
                    .flatten()
            })
            .collect();
        let mut changed = false;
        for (index, import) in imports.iter().enumerate() {
            if good[index] {
                continue;
            }
            if import
                .target
                .is_some_and(|target| bound.contains_key(&(target, import.name.as_str())))
            {
                good[index] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    imports
        .iter()
        .zip(&good)
        .find(|(_, good)| !**good)
        .map(|(import, _)| {
            format!(
                "the `use` of `{}` binds the ghost scalar name `{}` other than from this \
                 toolchain's crates",
                import.rendered, import.name
            )
        })
}
