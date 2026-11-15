// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Refuses a `Verified` answer for a function whose file can make a type
//! spelling denote a type other than the one this extraction reads.
//!
//! The syn lane reads type names as text. Some readers resolve a file-scope
//! `type` alias (`declared_width::FileTypeNames`, the source alias registry),
//! and others read the spelling as written (the closure definition-site
//! frame, the helper-contract parameter types, the receiver classifier). No
//! single place resolves every spelling the way rustc does, so for a file that
//!
//! * binds a primitive type name (`type u64 = u8;`, `struct u8;`, `mod u8`,
//!   `use core::primitive::u8 as u64;`, `use m::u64;`, `extern crate m as
//!   u64;`, an associated type `u8`) at file scope or in any function body or
//!   block, or in an inline module whose binding is reachable (see
//!   [`module_binding_is_reachable`]);
//! * renames a primitive type to another name (`use core::primitive::u8 as
//!   Byte;`), which no reader resolves;
//! * binds a ghost scalar name (`int`, `nat`, `real`) with a `type`,
//!   `struct`, `enum` or `union` item, or with a `use` that renames something
//!   else to it (a `mod real` cannot be spelled as a type);
//! * binds a std type name the lane gives std meaning
//!   ([`STD_MEANING_TYPE_NAMES`]: `struct Vec<T>`, `use m::MyVec as Vec;`,
//!   `type Vec<T> = MyVec<T>;`, `use heapless::Vec;`, `mod Vec`), with the
//!   same reach as a primitive binding. A `use` of that same name from a path
//!   that starts at `std`, `core` or `alloc`, and a `type` alias whose target
//!   is such a path ending in the alias's own name (`type Result<T> =
//!   std::result::Result<T, E>;`), are not rebindings: both still denote the
//!   std type;
//! * spells one of those std names through a path that does not start at
//!   `std`, `core`, `alloc` or a name the file imports from them (`m::Vec<u32>`
//!   for an out-of-line `mod m`, `heapless::Vec<u32, 2>`), since the readers
//!   read the last segment. An enum variant spelled through its own file enum
//!   (`Val::String(x)`) is not a type path and is not refused;
//! * declares a generic type parameter spelled like a primitive or ghost
//!   scalar, or like a std type the lane models by its bare name
//!   ([`MODELLED_STD_TYPE_NAMES`]); or
//! * declares a generic type parameter spelled like a name the file binds in
//!   the type namespace anywhere (`struct W; fn f<W: Tr>()`, `enum E`,
//!   `trait Tr`, `type W`, `mod W`, a `use`, an associated type). The lane
//!   looks up `W::five()` in the inherent impls by the spelling `W`, and lifts
//!   a method out of `impl<W> H<W>` without the impl's generics, so it can
//!   read the parameter as the file's type. A caller reads the callee's
//!   contract and a spec function's body the same way, so the whole file is
//!   refused, not only the function that declares the parameter; or
//! * has a glob import whose source the file does not show
//!   ([`OpaqueGlob`]: `use heapless::*;`, `use crate::prelude::*;`, `use
//!   super::*;` at file scope, a glob over an out-of-line `mod`), and spells
//!   a std-meaning type name, another prelude name the lane reads
//!   ([`PRELUDE_READ_NAMES`]: `Some`, `None`, `Ok`, `Err`, `Default`, `drop`)
//!   or a primitive type name bare where that glob's names reach. A glob
//!   shadows the prelude and the primitive types, so `Vec` under `use
//!   heapless::*;` is `heapless::Vec`, and `u64` under `use crate::other::*;`
//!   is `u8` when `other` holds `pub use core::primitive::u8 as u64;`. A
//!   glob in a module reaches the whole file, since another module can
//!   re-export it; a glob in a block reaches that block. A glob over a path
//!   that starts at `std`, `core` or `alloc`, or over an inline module or
//!   enum of the file, is read from the file instead (the other rules see
//!   what the module binds). A glob written in the tokens of a macro
//!   invocation or an attribute counts too; or
//! * has such a glob from outside this toolchain's crates and spells a ghost
//!   scalar name bare where it reaches, or a `use` that binds a ghost scalar
//!   name other than from those crates, directly or through `use` items of
//!   the file's inline modules (`pub type int = u8;` in the glob's source); or
//! * spells a type name the file declares (a `struct`, `enum`, `union` or
//!   `type` item; a std-meaning name is the std-name bullet's above) where it
//!   need not denote that declaration: a `use` binds it to another item or
//!   from a path that does not lead to a declaration or an import of it in
//!   the file, a path reaches it through segments that do not lead there, or
//!   a glob from outside the file reaches a bare spelling of it and the
//!   glob's own scope neither declares nor imports it. The lane reads
//!   a declared type by its name, whatever module holds it, so beside `mod a
//!   { pub type W = u64; }` it read the `W` of `use c::V as W;` and of `type
//!   V = other::W;` as `a::W` (see `declared_names`). A file into which the
//!   crate lane copied the type items of the crate's other files leaves the
//!   copied names to `crate_siblings`,
//!
//! a `Verified` answer cannot be shown sound and is refused. A refutation and
//! an earlier refusal are kept unchanged: neither can be a false `Verified`.
//!
//! A rebinding that no syntax shows (a macro expansion, a third-party derive
//! or attribute macro) is refused by `unread_items`. Not covered: a `core::` /
//! `std::` path prefix captured by `mod core`, `use m as core`, `extern
//! crate self as core` or a glob that imports a module of that name, except
//! where the path then spells a type name the file declares
//! (`core::primitive::u8` beside `mod primitive { pub type u8 = u64; }`),
//! which the declared-name rule refuses. These are the recorded residuals of
//! the `let` annotation width lane, which turns itself off for such files.

use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::{Spacing, TokenStream, TokenTree};
use quote::ToTokens;
use syn::visit::Visit;
use syn::{File, ItemFn};

mod crate_siblings;
mod declared_names;
mod self_paths;

pub use crate_siblings::{crate_sibling_view, CrateSiblingView};

/// The tag every refusal from this module starts with.
pub(super) const TYPE_NAME_REBINDING_TAG: &str = "type-name rebinding";

/// Rust's primitive type names.
const PRIMITIVE_TYPE_NAMES: &[&str] = &[
    "bool", "char", "str", "f16", "f32", "f64", "f128", "u8", "u16", "u32", "u64", "u128", "usize",
    "i8", "i16", "i32", "i64", "i128", "isize",
];

/// The ghost scalar names the lane reads as mathematical types. A plain
/// `use path::int;` is how a file brings them into scope, so only an item or a
/// `use` that renames another name to one of them counts as a rebinding.
const GHOST_SCALAR_NAMES: &[&str] = &["int", "nat", "real"];

/// Std and ghost type names the lane reads by their bare spelling. A generic
/// type parameter spelled like one of these is read as that type.
const MODELLED_STD_TYPE_NAMES: &[&str] = &[
    "Option",
    "Result",
    "Vec",
    "VecDeque",
    "String",
    "Box",
    "Rc",
    "Arc",
    "Cell",
    "RefCell",
    "HashMap",
    "HashSet",
    "BTreeMap",
    "BTreeSet",
    "Seq",
    "Set",
    "Map",
    "Multiset",
    "Ghost",
    "Tracked",
    "PhantomData",
];

/// The std types in [`MODELLED_STD_TYPE_NAMES`] whose spelling the lane gives
/// std meaning: a constructor, a method, a view or a transparent wrapper
/// (`Vec::new()`, `v.len()`, `*Box::new(x)`). Left out: `Cell` and `RefCell`,
/// which only the interior-mutability classifier reads, and it treats a type
/// it cannot show free of interior mutability as not free; and the ghost
/// names, whose readers consult the file's own shadowing
/// (`VerificationContext::spec_name_is_shadowed`).
const STD_MEANING_TYPE_NAMES: &[&str] = &[
    "Option",
    "Result",
    "Vec",
    "VecDeque",
    "String",
    "Box",
    "Rc",
    "Arc",
    "HashMap",
    "HashSet",
    "BTreeMap",
    "BTreeSet",
    "PhantomData",
];

/// Prelude names outside [`STD_MEANING_TYPE_NAMES`] that the lane reads with
/// their std meaning when spelled bare: the `Option` and `Result` variants,
/// `Default::default()` and `drop(x)`. A glob import can bind these names too.
const PRELUDE_READ_NAMES: &[&str] = &["Some", "None", "Ok", "Err", "Default", "drop"];

/// The crate roots whose items are the std types themselves.
const STD_ROOTS: &[&str] = &["std", "core", "alloc"];

fn is_primitive(name: &str) -> bool {
    PRIMITIVE_TYPE_NAMES.contains(&name)
}

fn has_std_meaning(name: &str) -> bool {
    STD_MEANING_TYPE_NAMES.contains(&name)
}

fn is_std_root(name: &str) -> bool {
    STD_ROOTS.contains(&name)
}

fn is_ghost_scalar(name: &str) -> bool {
    GHOST_SCALAR_NAMES.contains(&name)
}

/// True for a name the lane reads with a fixed meaning wherever it is spelled
/// bare: a primitive or ghost scalar type, a std type it models, or a prelude
/// name it reads ([`PRELUDE_READ_NAMES`]).
pub(super) fn is_lane_read_name(name: &str) -> bool {
    is_primitive(name)
        || is_ghost_scalar(name)
        || MODELLED_STD_TYPE_NAMES.contains(&name)
        || PRELUDE_READ_NAMES.contains(&name)
}

fn unraw(ident: &syn::Ident) -> String {
    syn::ext::IdentExt::unraw(ident).to_string()
}

/// The refusal message for a `Verified` answer of `func`, or `None` when no
/// construct in the file (or in `func`, when there is no file) can make a type
/// spelling denote another type. See the module documentation.
pub(super) fn verified_refusal(file: Option<&File>, func: &ItemFn) -> Option<String> {
    verified_refusal_with_outside_types(file, func, &BTreeSet::new())
}

/// [`verified_refusal`] for a file that holds copies of type items declared
/// in other files of its crate, whose names are `outside`. A spelling of one
/// of those names is the crate lane's to check (`crate_siblings`).
pub(super) fn verified_refusal_with_outside_types(
    file: Option<&File>,
    func: &ItemFn,
    outside: &BTreeSet<String>,
) -> Option<String> {
    let mut scan = Scan::default();
    if let Some(file) = file {
        scan.items(&file.items, Scope::File);
    }
    // The verified function may be a transformed copy of its file node.
    scan.item_fn(func, Scope::File);
    let hazard = scan.hazard(file, func, outside)?;
    Some(format!(
        "{TYPE_NAME_REBINDING_TAG}: {hazard}, so a type spelling in this file need not denote \
         the type this extraction reads it as. A `Verified` answer is refused; a refutation \
         would be kept"
    ))
}

/// The construct of `file` that can make a type spelling in it denote a type
/// other than the one this extraction reads, described; `None` when there is
/// none. See the module documentation.
fn file_hazard(file: &File) -> Option<String> {
    let probe: ItemFn = syn::parse_quote! {
        fn __trust_vc_file_probe() {}
    };
    let mut scan = Scan::default();
    scan.items(&file.items, Scope::File);
    scan.hazard(Some(file), &probe, &BTreeSet::new())
}

/// Every generic type parameter name declared anywhere in the file, or in
/// `func` when there is no file (`func` is always scanned: it may be a
/// transformed copy of its file node).
pub(super) fn generic_type_param_names(file: Option<&File>, func: &ItemFn) -> BTreeSet<String> {
    let mut scan = Scan::default();
    if let Some(file) = file {
        scan.items(&file.items, Scope::File);
    }
    scan.item_fn(func, Scope::File);
    scan.generic_params
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Scope {
    /// File scope, a function body or a block: a binding here is read by the
    /// bare spellings in its scope.
    File,
    /// Inside an inline `mod`. See [`module_binding_is_reachable`].
    Module(usize),
}

#[derive(Default)]
struct Scan {
    /// `(name, what, scope)` for every binding of a primitive or ghost scalar
    /// name in the type namespace.
    bindings: Vec<(String, String, Scope)>,
    /// A `use` that renames a primitive type to another name.
    primitive_renames: Vec<String>,
    /// Every generic type parameter name.
    generic_params: BTreeSet<String>,
    /// The tokens of each inline module's items other than the name of a
    /// binding, by module index.
    module_tokens: Vec<TokenStream>,
    has_glob_import: bool,
    /// `(name, what, scope)` for every binding of a std-meaning type name
    /// that need not denote the std type.
    std_name_bindings: Vec<(String, String, Scope)>,
    /// Every name a `use` imports from a path that starts at a std root
    /// (`fmt` in `use std::fmt;`).
    std_import_names: BTreeSet<String>,
    /// Every name bound in the type namespace other than by such a `use`.
    other_bound_names: BTreeSet<String>,
    /// Every enum's variant names, by the enum's name.
    enum_variants: BTreeMap<String, BTreeSet<String>>,
    /// Every associated type name.
    associated_type_names: BTreeSet<String>,
}

impl Scan {
    /// Record a binding of `name`. A ghost scalar is read only as a type, so it
    /// counts only for a binding a type position can resolve to (a `type`,
    /// `struct`, `enum` or `union` item, or a `use`): a `mod real` or `trait
    /// real` cannot be spelled as a type. A primitive name counts for every
    /// binding, since `u8::MAX` and the other associated paths resolve
    /// through a module or trait of that name too.
    fn bind(&mut self, name: String, what: &str, scope: Scope, type_position: bool) {
        if is_primitive(&name) || (type_position && is_ghost_scalar(&name)) {
            self.bindings.push((name, what.to_string(), scope));
        }
    }

    /// Record `name`, bound by something other than a `use` from a std root,
    /// and count it when it is a std-meaning name.
    fn bind_other(&mut self, name: &str, what: &str, scope: Scope) {
        if has_std_meaning(name) {
            self.std_name_bindings
                .push((name.to_string(), what.to_string(), scope));
        }
        self.other_bound_names.insert(name.to_string());
    }

    fn items(&mut self, items: &[syn::Item], scope: Scope) {
        for item in items {
            self.item(item, scope);
        }
    }

    fn item(&mut self, item: &syn::Item, scope: Scope) {
        let (ident, what, type_position) = match item {
            syn::Item::Use(it) => {
                self.use_tree(&it.tree, scope, &[]);
                return;
            }
            syn::Item::ExternCrate(it) => {
                let name = it
                    .rename
                    .as_ref()
                    .map_or_else(|| unraw(&it.ident), |(_, rename)| unraw(rename));
                self.bind_other(&name, "an `extern crate` item", scope);
                self.bind(name, "an `extern crate` item", scope, false);
                return;
            }
            syn::Item::Mod(it) => {
                self.bind_other(&unraw(&it.ident), "a `mod` item", scope);
                self.bind(unraw(&it.ident), "a `mod` item", scope, false);
                if let Some((_, inner)) = &it.content {
                    let index = self.module_tokens.len();
                    let tokens = inner.iter().map(reading_tokens).collect();
                    self.module_tokens.push(tokens);
                    self.items(inner, Scope::Module(index));
                }
                return;
            }
            syn::Item::Type(it) => (Some(&it.ident), "a `type` item", true),
            syn::Item::Struct(it) => (Some(&it.ident), "a `struct` item", true),
            syn::Item::Enum(it) => {
                self.enum_variants
                    .entry(unraw(&it.ident))
                    .or_default()
                    .extend(it.variants.iter().map(|variant| unraw(&variant.ident)));
                (Some(&it.ident), "an `enum` item", true)
            }
            syn::Item::Union(it) => (Some(&it.ident), "a `union` item", true),
            syn::Item::Trait(it) => (Some(&it.ident), "a `trait` item", false),
            syn::Item::TraitAlias(it) => (Some(&it.ident), "a trait alias", false),
            _ => (None, "", false),
        };
        if let Some(ident) = ident {
            let name = unraw(ident);
            let aliases_std_type =
                matches!(item, syn::Item::Type(it) if alias_names_its_std_type(it));
            if aliases_std_type {
                self.other_bound_names.insert(name.clone());
            } else {
                self.bind_other(&name, what, scope);
            }
            self.bind(name, what, scope, type_position);
        }
        // The item's interior: generics, fields, bodies, `impl` / `trait`
        // items, and every item nested in them.
        syn::visit::visit_item(&mut Walker { scan: self, scope }, item);
    }

    fn item_fn(&mut self, func: &ItemFn, scope: Scope) {
        syn::visit::visit_item_fn(&mut Walker { scan: self, scope }, func);
    }

    /// `prefix` holds the path segments above `tree`, from the root.
    fn use_tree(&mut self, tree: &syn::UseTree, scope: Scope, prefix: &[String]) {
        match tree {
            syn::UseTree::Path(path) => {
                let mut prefix = prefix.to_vec();
                prefix.push(unraw(&path.ident));
                self.use_tree(&path.tree, scope, &prefix);
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    self.use_tree(item, scope, prefix);
                }
            }
            syn::UseTree::Name(name) => {
                let name = unraw(&name.ident);
                // `use std::fmt::{self};` binds `fmt`.
                let bound = if name == "self" {
                    prefix.last().cloned().unwrap_or(name.clone())
                } else {
                    name.clone()
                };
                self.use_binding(prefix, &bound, &bound, "a `use` item", scope);
                // `use path::int;` is the ordinary way to bring the ghost
                // scalar into scope.
                if !is_ghost_scalar(&name) {
                    self.bind(name, "a `use` item", scope, true);
                }
            }
            syn::UseTree::Rename(rename) => {
                let source = unraw(&rename.ident);
                let target = unraw(&rename.rename);
                let named_source = if source == "self" {
                    prefix.last().cloned().unwrap_or(source.clone())
                } else {
                    source.clone()
                };
                self.use_binding(
                    prefix,
                    &named_source,
                    &target,
                    "a `use ... as` rename",
                    scope,
                );
                if is_primitive(&source) && source != target {
                    self.primitive_renames
                        .push(format!("`{source} as {target}`"));
                }
                if !(is_ghost_scalar(&target) && source == target) {
                    self.bind(target, "a `use ... as` rename", scope, true);
                }
            }
            syn::UseTree::Glob(_) => self.has_glob_import = true,
        }
    }

    /// Record a `use` under `prefix` that binds `target` to the item named
    /// `source`. Only an import of the same name from a std root still denotes
    /// the std item.
    fn use_binding(
        &mut self,
        prefix: &[String],
        source: &str,
        target: &str,
        what: &str,
        scope: Scope,
    ) {
        if target == "_" {
            return;
        }
        let from_std = prefix.first().is_some_and(|root| is_std_root(root));
        if from_std && source == target {
            self.std_import_names.insert(target.to_string());
        } else {
            self.bind_other(target, what, scope);
        }
    }

    fn hazard(
        &self,
        file: Option<&File>,
        func: &ItemFn,
        outside: &BTreeSet<String>,
    ) -> Option<String> {
        if let Some(rename) = self.primitive_renames.first() {
            return Some(format!("a `use` renames a primitive type ({rename})"));
        }
        for (name, what, scope) in &self.bindings {
            let reachable = match scope {
                Scope::File => true,
                Scope::Module(index) => module_binding_is_reachable(
                    name,
                    &self.module_tokens[*index],
                    self.has_glob_import,
                    file,
                    func,
                ),
            };
            if reachable {
                return Some(format!("{what} binds the type name `{name}`"));
            }
        }
        for name in &self.generic_params {
            if is_primitive(name)
                || is_ghost_scalar(name)
                || MODELLED_STD_TYPE_NAMES.contains(&name.as_str())
            {
                return Some(format!(
                    "a generic type parameter is named `{name}`, the name of another type"
                ));
            }
            if self.other_bound_names.contains(name)
                || self.std_import_names.contains(name)
                || self.associated_type_names.contains(name)
            {
                return Some(format!(
                    "a generic type parameter is named `{name}`, a name the file also binds \
                     in the type namespace"
                ));
            }
        }
        for (name, what, scope) in &self.std_name_bindings {
            let reachable = match scope {
                Scope::File => true,
                Scope::Module(index) => module_binding_is_reachable(
                    name,
                    &self.module_tokens[*index],
                    self.has_glob_import,
                    file,
                    func,
                ),
            };
            if reachable {
                return Some(format!("{what} binds the std type name `{name}`"));
            }
        }
        // A `use` item is read by `use_binding` above; its paths are not
        // spellings of a type.
        let file_tokens = file.map_or_else(TokenStream::new, |file| {
            let mut file = file.clone();
            syn::visit_mut::VisitMut::visit_file_mut(&mut UseItemRemover, &mut file);
            file.to_token_stream()
        });
        let globs = opaque_globs(file, func);
        let mut func_without_uses = func.clone();
        syn::visit_mut::VisitMut::visit_item_fn_mut(&mut UseItemRemover, &mut func_without_uses);
        let func_tokens = func_without_uses.to_token_stream();
        for tokens in [file_tokens.clone(), func_tokens.clone()] {
            if let Some(path) = self.std_name_path_outside_std(tokens) {
                return Some(format!(
                    "the path `{path}` spells a std type name without starting at `std`, \
                     `core` or `alloc`"
                ));
            }
        }
        if let Some(name) =
            self_paths::self_path_not_variant(file, Some(func), &self.self_variants(), &|name| {
                has_std_meaning(name)
            })
        {
            return Some(format!(
                "the path `Self::{name}` spells a std type name where `Self` need not be an \
                 enum with a variant `{name}`"
            ));
        }
        let reaches: Vec<(OpaqueGlob, Vec<TokenStream>)> = globs
            .into_iter()
            .map(|glob| {
                let reach = match &glob.block {
                    None => vec![file_tokens.clone(), func_tokens.clone()],
                    Some(block) => {
                        let mut block = block.clone();
                        syn::visit_mut::VisitMut::visit_block_mut(&mut UseItemRemover, &mut block);
                        vec![block.to_token_stream()]
                    }
                };
                (glob, reach)
            })
            .collect();
        // A glob shadows the primitive types as it shadows the prelude: under
        // `use other::*;` where `other` holds `pub use core::primitive::u8 as
        // u64;`, the spelling `u64` is `u8`. The std and prelude names are
        // checked first, over every glob, so a file that spells both kinds is
        // refused naming the std one.
        let std_names: Vec<&str> = STD_MEANING_TYPE_NAMES
            .iter()
            .chain(PRELUDE_READ_NAMES)
            .copied()
            .collect();
        for names in [std_names.as_slice(), PRIMITIVE_TYPE_NAMES] {
            for (glob, reach) in &reaches {
                let spelled = names
                    .iter()
                    .filter(|name| !glob.std_imports.contains(**name))
                    .find(|name| {
                        reach
                            .iter()
                            .any(|tokens| spells(tokens.clone(), name, Spelling::Bare))
                    });
                if let Some(name) = spelled {
                    return Some(format!(
                        "the glob import `use {};` imports from outside this file and can bind \
                         `{name}`, which the file spells",
                        glob.rendered
                    ));
                }
            }
        }
        // A glob from outside this toolchain's crates can bind a ghost scalar
        // name (`pub type int = u8;`), which the lane reads as a mathematical
        // type.
        for (glob, reach) in &reaches {
            if glob
                .root
                .as_deref()
                .is_some_and(|root| declared_names::TOOLCHAIN_ROOTS.contains(&root))
            {
                continue;
            }
            let spelled = GHOST_SCALAR_NAMES.iter().find(|name| {
                reach
                    .iter()
                    .any(|tokens| spells(tokens.clone(), name, Spelling::Bare))
            });
            if let Some(name) = spelled {
                return Some(format!(
                    "the glob import `use {};` imports from outside this toolchain's crates and \
                     can bind `{name}`, which the file spells",
                    glob.rendered
                ));
            }
        }
        if let Some(hazard) = declared_names::ghost_scalar_import_hazard(file, func) {
            return Some(hazard);
        }
        // The rules above read a path that starts at a toolchain crate's name
        // as that crate's; a file that binds the name to something else
        // (`mod vstd;` beside `pub type int = u8;`) makes it a local path.
        if let Some(binding) = declared_names::rebound_toolchain_root(file, func) {
            return Some(format!(
                "the file binds {binding}, so a path through that name need not reach that crate"
            ));
        }
        // A std type name the lane gives std meaning is the std-name rule's,
        // above: it refuses every declaration of one but an alias of the std
        // type itself (`type Result<T> = std::result::Result<T, E>;`), every
        // `use` that binds one other than from std, and every path to one
        // other than through std, a name imported from std (`fmt::Result`
        // under `use std::fmt;`) or a variant of a file enum.
        let declared: BTreeSet<String> = declared_names::declared_type_names(file, func)
            .into_iter()
            .filter(|name| !outside.contains(name) && !has_std_meaning(name))
            .collect();
        let variants = self.self_variants();
        if let Some(hazard) = declared_names::declared_name_hazard(file, func, &declared, &variants)
        {
            return Some(hazard);
        }
        // A glob from outside the file can bind a name the file declares in
        // another scope: beside `mod a { pub struct W; }`, the `W` of `fn f(w:
        // W)` under `use other::*;` is `other::W`, while the lane reads
        // `a::W`. A declaration or an import of that name in the glob's own
        // scope wins over the glob.
        if declared.is_empty() || reaches.is_empty() {
            return None;
        }
        let masked_file = file.map_or_else(TokenStream::new, |file| {
            let mut file = file.clone();
            syn::visit_mut::VisitMut::visit_file_mut(&mut UseItemRemover, &mut file);
            syn::visit_mut::VisitMut::visit_file_mut(&mut DeclaredIdentMasker, &mut file);
            file.to_token_stream()
        });
        let mut masked_func = func.clone();
        syn::visit_mut::VisitMut::visit_item_fn_mut(&mut UseItemRemover, &mut masked_func);
        syn::visit_mut::VisitMut::visit_item_fn_mut(&mut DeclaredIdentMasker, &mut masked_func);
        let masked_func = masked_func.to_token_stream();
        for (glob, _) in &reaches {
            let reach = match &glob.block {
                None => vec![masked_file.clone(), masked_func.clone()],
                Some(block) => {
                    let mut block = block.clone();
                    syn::visit_mut::VisitMut::visit_block_mut(&mut UseItemRemover, &mut block);
                    syn::visit_mut::VisitMut::visit_block_mut(&mut DeclaredIdentMasker, &mut block);
                    vec![block.to_token_stream()]
                }
            };
            let spelled = declared
                .iter()
                .filter(|name| !glob.bound_here.contains(*name))
                .find(|name| {
                    reach
                        .iter()
                        .any(|tokens| spells(tokens.clone(), name, Spelling::Bare))
                });
            if let Some(name) = spelled {
                return Some(format!(
                    "the glob import `use {};` imports from outside this file and can bind \
                     `{name}`, a type name this file declares in another scope, which the file \
                     spells",
                    glob.rendered
                ));
            }
        }
        None
    }

    /// The file's enums and associated types, which decide where `Self::W`
    /// names a variant.
    fn self_variants(&self) -> self_paths::SelfVariants<'_> {
        self_paths::SelfVariants {
            enums: &self.enum_variants,
            associated: &self.associated_type_names,
        }
    }

    /// The first path in `tokens` (at any group depth) that spells a
    /// std-meaning name after a `::` and need not denote the std type,
    /// rendered.
    fn std_name_path_outside_std(&self, tokens: TokenStream) -> Option<String> {
        let flat: Vec<TokenTree> = tokens.into_iter().collect();
        for (index, tree) in flat.iter().enumerate() {
            match tree {
                TokenTree::Group(group) => {
                    if let Some(path) = self.std_name_path_outside_std(group.stream()) {
                        return Some(path);
                    }
                }
                TokenTree::Ident(ident) => {
                    let name = unraw(ident);
                    if !has_std_meaning(&name)
                        || index < 2
                        || !is_path_sep(&flat[index - 2], &flat[index - 1])
                    {
                        continue;
                    }
                    let segments = path_segments(&flat[..index]);
                    if !self.names_std_item_or_variant(segments.as_deref(), &name) {
                        let prefix = segments.map_or_else(|| "..".to_string(), |s| s.join("::"));
                        return Some(format!("{prefix}::{name}"));
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Whether a path spelling the std-meaning `name` after `segments` denotes
    /// the std item, or a variant of a file enum (`Val::String`; the
    /// `self_paths` rule reads `Self::String`). `None` is a path with a
    /// segment that is not a plain identifier.
    fn names_std_item_or_variant(&self, segments: Option<&[String]>, name: &str) -> bool {
        match segments {
            Some([first, ..]) if is_std_root(first) => true,
            Some([first, ..])
                if self.std_import_names.contains(first)
                    && !self.other_bound_names.contains(first) =>
            {
                true
            }
            // Left to `self_paths`, which knows what `Self` is where the path
            // is written.
            Some([owner]) if owner == "Self" => true,
            Some([owner]) => {
                !self.associated_type_names.contains(name)
                    && self
                        .enum_variants
                        .get(owner)
                        .is_some_and(|variants| variants.contains(name))
            }
            _ => false,
        }
    }
}

/// Replaces the name each `struct`, `enum`, `union`, `type`, `trait` and `mod`
/// item declares, and each enum variant's name, so that the tokens left spell
/// a name only where they read it.
struct DeclaredIdentMasker;

impl syn::visit_mut::VisitMut for DeclaredIdentMasker {
    fn visit_item_mut(&mut self, item: &mut syn::Item) {
        let placeholder = syn::Ident::new("__trust_vc_bound_name", proc_macro2::Span::call_site());
        match item {
            syn::Item::Struct(it) => it.ident = placeholder,
            syn::Item::Enum(it) => {
                it.ident = placeholder.clone();
                for variant in &mut it.variants {
                    variant.ident = placeholder.clone();
                }
            }
            syn::Item::Union(it) => it.ident = placeholder,
            syn::Item::Type(it) => it.ident = placeholder,
            syn::Item::Trait(it) => it.ident = placeholder,
            syn::Item::Mod(it) => it.ident = placeholder,
            _ => {}
        }
        syn::visit_mut::visit_item_mut(self, item);
    }
}

/// Removes every `use` item, at any depth.
struct UseItemRemover;

impl syn::visit_mut::VisitMut for UseItemRemover {
    fn visit_file_mut(&mut self, file: &mut File) {
        file.items.retain(|item| !matches!(item, syn::Item::Use(_)));
        syn::visit_mut::visit_file_mut(self, file);
    }

    fn visit_item_mod_mut(&mut self, item: &mut syn::ItemMod) {
        if let Some((_, items)) = &mut item.content {
            items.retain(|item| !matches!(item, syn::Item::Use(_)));
        }
        syn::visit_mut::visit_item_mod_mut(self, item);
    }

    fn visit_block_mut(&mut self, block: &mut syn::Block) {
        block
            .stmts
            .retain(|stmt| !matches!(stmt, syn::Stmt::Item(syn::Item::Use(_))));
        syn::visit_mut::visit_block_mut(self, block);
    }
}

/// Keywords that can stand right before a leading `::` (`&mut ::std::x`,
/// `x as ::core::y`); none of them is a path segment.
const KEYWORDS_BEFORE_LEADING_PATH_SEP: &[&str] = &[
    "as", "box", "break", "const", "dyn", "else", "for", "if", "impl", "in", "let", "match",
    "move", "mut", "ref", "return", "static", "type", "unsafe", "where", "while", "yield",
];

/// The identifier segments of the path that ends just after `before`, from the
/// first, without the last one; `before` holds every token up to the path's
/// last `::`. A leading `::` is dropped. `None` when a segment is not a plain
/// identifier (`<T as Tr>::`, `Foo::<T>::`).
fn path_segments(before: &[TokenTree]) -> Option<Vec<String>> {
    let mut segments = Vec::new();
    let mut end = before.len();
    // `before[..end]` ends with `::`.
    while end >= 2 && is_path_sep(&before[end - 2], &before[end - 1]) {
        end -= 2;
        let Some(previous) = end.checked_sub(1).map(|at| &before[at]) else {
            break;
        };
        match previous {
            TokenTree::Ident(segment) => {
                let lifetime = end >= 2
                    && matches!(&before[end - 2], TokenTree::Punct(p) if p.as_char() == '\'');
                let segment = unraw(segment);
                if lifetime || KEYWORDS_BEFORE_LEADING_PATH_SEP.contains(&segment.as_str()) {
                    break;
                }
                segments.push(segment);
                end -= 1;
            }
            // A `>` that closes generic arguments; the `>` of `=>` and `->`
            // ends the path at a leading `::` instead.
            TokenTree::Punct(p) if p.as_char() == '>' => {
                let arrow = end >= 2
                    && matches!(
                        &before[end - 2],
                        TokenTree::Punct(q)
                            if matches!(q.as_char(), '=' | '-') && q.spacing() == Spacing::Joint
                    );
                if arrow {
                    break;
                }
                return None;
            }
            // Anything else ends the path at a leading `::`.
            _ => break,
        }
    }
    segments.reverse();
    Some(segments)
}

/// Whether a `type` item names the std type of its own name, with its own
/// type parameters as that type's leading arguments, in order
/// (`type Result<T> = std::result::Result<T, E>;`). A spelling `Result<A>` then
/// denotes `std::result::Result<A, E>`, whose leading argument is the one a
/// reader of the spelling sees. An alias that reorders or drops its parameters
/// (`type Result<E, T> = std::result::Result<T, E>;`) does not qualify.
fn alias_names_its_std_type(item: &syn::ItemType) -> bool {
    let syn::Type::Path(target) = &*item.ty else {
        return false;
    };
    if target.qself.is_some() {
        return false;
    }
    let segments = &target.path.segments;
    let (Some(first), Some(last)) = (segments.first(), segments.last()) else {
        return false;
    };
    if segments.len() < 2
        || !is_std_root(&unraw(&first.ident))
        || unraw(&last.ident) != unraw(&item.ident)
        || segments
            .iter()
            .take(segments.len() - 1)
            .any(|segment| !segment.arguments.is_none())
    {
        return false;
    }
    let mut params = Vec::new();
    for param in &item.generics.params {
        let syn::GenericParam::Type(param) = param else {
            return false;
        };
        params.push(unraw(&param.ident));
    }
    if params.is_empty() {
        return true;
    }
    let syn::PathArguments::AngleBracketed(args) = &last.arguments else {
        return false;
    };
    let leading: Vec<Option<String>> = args
        .args
        .iter()
        .take(params.len())
        .map(|arg| match arg {
            syn::GenericArgument::Type(syn::Type::Path(path))
                if path.qself.is_none() && path.path.segments.len() == 1 =>
            {
                path.path.get_ident().map(unraw)
            }
            _ => None,
        })
        .collect();
    leading.len() == params.len()
        && leading
            .iter()
            .zip(&params)
            .all(|(arg, param)| arg.as_ref() == Some(param))
}

/// Walks the interior of one item: every nested item, generic parameter and
/// associated type it holds. A nested item binds in the scope the walk is in:
/// an item or `use` in a body or block is read by the spellings of that body.
struct Walker<'a> {
    scan: &'a mut Scan,
    scope: Scope,
}

impl<'ast> Visit<'ast> for Walker<'_> {
    fn visit_item(&mut self, item: &'ast syn::Item) {
        self.scan.item(item, self.scope);
    }

    fn visit_type_param(&mut self, param: &'ast syn::TypeParam) {
        self.scan.generic_params.insert(unraw(&param.ident));
        syn::visit::visit_type_param(self, param);
    }

    fn visit_impl_item_type(&mut self, item: &'ast syn::ImplItemType) {
        self.scan.associated_type_names.insert(unraw(&item.ident));
        self.scan
            .bind(unraw(&item.ident), "an associated type", self.scope, false);
        syn::visit::visit_impl_item_type(self, item);
    }

    fn visit_trait_item_type(&mut self, item: &'ast syn::TraitItemType) {
        self.scan.associated_type_names.insert(unraw(&item.ident));
        self.scan
            .bind(unraw(&item.ident), "an associated type", self.scope, false);
        syn::visit::visit_trait_item_type(self, item);
    }
}

/// A glob `use` whose source this file does not show, so any name may come
/// from it.
struct OpaqueGlob {
    /// The glob as written after `use` (`heapless::*`).
    rendered: String,
    /// The block that holds the glob, whose spellings are the only ones it
    /// reaches; `None` for a glob in a module, which reaches every spelling in
    /// the file (another module can glob-import that module).
    block: Option<syn::Block>,
    /// The names a non-glob `use` from a std root binds in the glob's own
    /// scope, which win over the glob there. Kept only for a glob at file
    /// scope or in a block: every scope that can import from those sees the
    /// same binding, while an inline module can re-export the glob's names
    /// without its private `use`.
    std_imports: BTreeSet<String>,
    /// Every name an item or a non-glob `use` binds in the type namespace of
    /// the glob's own scope, which wins over the glob there. Kept, as
    /// `std_imports` is, only for a glob at file scope or in a block.
    bound_here: BTreeSet<String>,
    /// The first segment of the glob's path (`heapless` in `use
    /// ::heapless::*;`), or `None` when the glob was not parsed as a path.
    root: Option<String>,
}

/// Every glob `use` in `file` and `func` whose source is not a std root or an
/// inline module or enum of the file. `func` is scanned as if it were at file
/// scope; it may be a transformed copy of its file node.
fn opaque_globs(file: Option<&File>, func: &ItemFn) -> Vec<OpaqueGlob> {
    let mut scan = GlobScan::default();
    if let Some(file) = file {
        scan.frames.push(Frame::Module(&file.items));
        scan.visit_file(file);
    }
    scan.visit_item_fn(func);
    scan.globs
}

/// Every glob `use` in `file` whose source is not a std root or an inline
/// module or enum of the file, as written after `use` (`heapless::*`).
pub(super) fn opaque_glob_renderings(file: &File) -> Vec<String> {
    let probe: ItemFn = syn::parse_quote! {
        fn __opaque_glob_probe() {}
    };
    opaque_globs(Some(file), &probe)
        .into_iter()
        .map(|glob| glob.rendered)
        .collect()
}

/// A `use` whose source the file does not show.
pub(super) struct OpaqueImport {
    /// The path as written after `use` (`other::MyClone`, `heapless::*`).
    pub(super) rendered: String,
    /// The block that holds the `use`, the only code its names reach; `None`
    /// for a `use` in a module or in macro or attribute tokens, which reaches
    /// the whole file.
    pub(super) block: Option<syn::Block>,
}

/// Every `use` in `file` and `func` whose source the file does not show: the
/// globs of [`opaque_globs`] and every name imported from a path that does
/// not start at a std root or name an inline module or enum of the file
/// (`other::MyClone`, `crate::m::Tr`). A `use` of a single segment (`use
/// other;`) imports a crate or module, never a trait, and is left out.
pub(super) fn opaque_imports(file: Option<&File>, func: &ItemFn) -> Vec<OpaqueImport> {
    let mut scan = GlobScan::default();
    if let Some(file) = file {
        scan.frames.push(Frame::Module(&file.items));
        scan.visit_file(file);
    }
    scan.visit_item_fn(func);
    scan.globs
        .into_iter()
        .map(|glob| OpaqueImport {
            rendered: glob.rendered,
            block: glob.block,
        })
        .chain(scan.named)
        .collect()
}

/// A scope that a `use` can sit in.
#[derive(Clone, Copy)]
enum Frame<'ast> {
    /// The file's own scope (always the first frame) or an inline module.
    Module(&'ast [syn::Item]),
    Block(&'ast syn::Block),
}

/// What a path segment names in a scope.
#[derive(Clone, Copy)]
enum Target<'ast> {
    Module(&'ast [syn::Item]),
    Enum,
}

/// Walks the file with the scopes around each `use`.
#[derive(Default)]
struct GlobScan<'ast> {
    /// The enclosing scopes, outermost first. When the file is scanned, the
    /// first frame is its own scope.
    frames: Vec<Frame<'ast>>,
    globs: Vec<OpaqueGlob>,
    /// Every non-glob `use` of a name whose source the file does not show.
    named: Vec<OpaqueImport>,
}

impl<'ast> Visit<'ast> for GlobScan<'ast> {
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

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        syn::visit::visit_macro(self, mac);
        self.globs_in_tokens(mac.tokens.clone());
    }

    fn visit_meta_list(&mut self, list: &'ast syn::MetaList) {
        syn::visit::visit_meta_list(self, list);
        self.globs_in_tokens(list.tokens.clone());
    }

    fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
        let leading_colon = item.leading_colon.is_some();
        let mut leaves = Vec::new();
        named_leaves(&item.tree, &mut Vec::new(), &mut leaves);
        for (prefix, leaf) in leaves {
            if prefix.is_empty() || self.resolves_to_std_or_file(leading_colon, &prefix) {
                continue;
            }
            let block = match self.frames.last() {
                Some(Frame::Block(block)) => Some((*block).clone()),
                _ => None,
            };
            self.named.push(OpaqueImport {
                rendered: format!(
                    "{}{}::{leaf}",
                    if leading_colon { "::" } else { "" },
                    prefix.join("::")
                ),
                block,
            });
        }
        let mut prefixes = Vec::new();
        glob_prefixes(&item.tree, &mut Vec::new(), &mut prefixes);
        for prefix in prefixes {
            if self.resolves_to_std_or_file(leading_colon, &prefix) {
                continue;
            }
            let rendered = format!(
                "{}{}::*",
                if leading_colon { "::" } else { "" },
                prefix.join("::")
            );
            let (block, std_imports, bound_here) = match self.frames.last() {
                Some(Frame::Block(block)) => (
                    Some((*block).clone()),
                    std_use_names(block_items(block)),
                    type_namespace_names(block_items(block)),
                ),
                Some(Frame::Module(items)) if self.frames.len() == 1 => (
                    None,
                    std_use_names(items.iter()),
                    type_namespace_names(items.iter()),
                ),
                _ => (None, BTreeSet::new(), BTreeSet::new()),
            };
            self.globs.push(OpaqueGlob {
                rendered,
                block,
                std_imports,
                bound_here,
                root: prefix.first().cloned(),
            });
        }
    }
}

impl<'ast> GlobScan<'ast> {
    /// Records each glob `use` written in the tokens of a macro invocation or
    /// an attribute (`assert!({ use other::*; .. })`, a `macro_rules!` body).
    /// The scopes inside those tokens are not walked, so only a glob over a
    /// std root is read as such; any other glob reaches the whole file.
    fn globs_in_tokens(&mut self, tokens: TokenStream) {
        let flat: Vec<TokenTree> = tokens.into_iter().collect();
        for (index, tree) in flat.iter().enumerate() {
            match tree {
                TokenTree::Group(group) => self.globs_in_tokens(group.stream()),
                TokenTree::Ident(ident) if ident == "use" => {
                    let end = flat[index..]
                        .iter()
                        .position(|tree| is_punct(tree, ';'))
                        .map_or(flat.len(), |offset| index + offset + 1);
                    let statement: TokenStream = flat[index..end].iter().cloned().collect();
                    let globs = match syn::parse2::<syn::ItemUse>(statement.clone()) {
                        Ok(item) => {
                            let leading = if item.leading_colon.is_some() {
                                "::"
                            } else {
                                ""
                            };
                            let mut leaves = Vec::new();
                            named_leaves(&item.tree, &mut Vec::new(), &mut leaves);
                            for (prefix, leaf) in leaves {
                                if prefix.first().is_some_and(|root| !is_std_root(root)) {
                                    self.named.push(OpaqueImport {
                                        rendered: format!("{leading}{}::{leaf}", prefix.join("::")),
                                        block: None,
                                    });
                                }
                            }
                            let mut prefixes = Vec::new();
                            glob_prefixes(&item.tree, &mut Vec::new(), &mut prefixes);
                            prefixes
                                .into_iter()
                                .filter(|prefix| {
                                    !prefix.first().is_some_and(|root| is_std_root(root))
                                })
                                .map(|prefix| {
                                    (
                                        format!("{leading}{}::*", prefix.join("::")),
                                        prefix.first().cloned(),
                                    )
                                })
                                .collect()
                        }
                        // Not a `use` item the parser reads (`use $crate::*;`
                        // in a `macro_rules!` body): any `*` in it may be a
                        // glob, and any name it imports may come from anywhere.
                        Err(_) => {
                            let glob = contains_punct(statement.clone(), '*');
                            let rendered = statement.to_string();
                            let rendered = rendered
                                .trim_start_matches("use")
                                .trim_end_matches(';')
                                .trim();
                            if glob {
                                vec![(rendered.to_string(), None)]
                            } else {
                                self.named.push(OpaqueImport {
                                    rendered: rendered.to_string(),
                                    block: None,
                                });
                                Vec::new()
                            }
                        }
                    };
                    for (rendered, root) in globs {
                        self.globs.push(OpaqueGlob {
                            rendered,
                            block: None,
                            std_imports: BTreeSet::new(),
                            bound_here: BTreeSet::new(),
                            root,
                        });
                    }
                }
                _ => {}
            }
        }
    }

    /// Whether `use prefix::*;`, written in the innermost frame, imports from a
    /// std root or from an inline module or enum of the file. Anything this
    /// cannot settle from the file's own items (an extern crate, `crate::`,
    /// `super` above the file, an out-of-line `mod`, a name another `use`
    /// binds) is not.
    fn resolves_to_std_or_file(&self, leading_colon: bool, prefix: &[String]) -> bool {
        if prefix.first().is_some_and(|root| is_std_root(root)) {
            return true;
        }
        resolve_in_frames(&self.frames, leading_colon, prefix).is_some()
    }
}

/// What the path `prefix`, written in the innermost of `frames`, names in the
/// file: an inline module or an enum. `None` for anything the file's own
/// items cannot settle: a std root, an extern crate, `crate::`, `super` above
/// the file, an out-of-line `mod`, a name another `use` binds.
fn resolve_in_frames<'ast>(
    frames: &[Frame<'ast>],
    leading_colon: bool,
    prefix: &[String],
) -> Option<Target<'ast>> {
    let (first, rest) = prefix.split_first()?;
    if leading_colon || is_std_root(first) {
        return None;
    }
    let (mut target, rest) = match first.as_str() {
        "crate" => return None,
        "self" | "super" => {
            let mut module = enclosing_module(frames, frames.len())?;
            let mut rest = if first == "self" { rest } else { prefix };
            while let Some((segment, tail)) = rest.split_first() {
                if segment != "super" {
                    break;
                }
                module = enclosing_module(frames, module)?;
                rest = tail;
            }
            let Frame::Module(items) = frames[module] else {
                return None;
            };
            (Target::Module(items), rest)
        }
        name => (lookup(frames, name)?, rest),
    };
    for segment in rest {
        let Target::Module(items) = target else {
            return None;
        };
        target = type_namespace_target(items.iter(), segment)?;
    }
    Some(target)
}

/// The index of the innermost module frame below `below`.
fn enclosing_module(frames: &[Frame<'_>], below: usize) -> Option<usize> {
    frames[..below]
        .iter()
        .rposition(|frame| matches!(frame, Frame::Module(_)))
}

/// What `name` names at the innermost frame: the blocks around it, from the
/// innermost out, then the module that holds them.
fn lookup<'ast>(frames: &[Frame<'ast>], name: &str) -> Option<Target<'ast>> {
    for frame in frames.iter().rev() {
        match frame {
            Frame::Block(block) => {
                let items: Vec<&syn::Item> = block_items(block).collect();
                if items.iter().any(|item| binds_in_type_namespace(item, name)) {
                    return type_namespace_target(items.into_iter(), name);
                }
            }
            Frame::Module(items) => return type_namespace_target(items.iter(), name),
        }
    }
    None
}

/// The items among a block's statements.
fn block_items(block: &syn::Block) -> impl Iterator<Item = &syn::Item> {
    block.stmts.iter().filter_map(|stmt| match stmt {
        syn::Stmt::Item(item) => Some(item),
        _ => None,
    })
}

/// What `name` names among `items`: an inline module or an enum declared once,
/// and nothing else.
fn type_namespace_target<'ast>(
    items: impl Iterator<Item = &'ast syn::Item>,
    name: &str,
) -> Option<Target<'ast>> {
    let mut found = items.filter(|item| binds_in_type_namespace(item, name));
    let target = match found.next()? {
        syn::Item::Mod(it) => Target::Module(&it.content.as_ref()?.1),
        syn::Item::Enum(_) => Target::Enum,
        _ => return None,
    };
    found.next().is_none().then_some(target)
}

/// Whether `item` binds `name` in the type namespace.
fn binds_in_type_namespace(item: &syn::Item, name: &str) -> bool {
    let ident = match item {
        syn::Item::Mod(it) => &it.ident,
        syn::Item::Enum(it) => &it.ident,
        syn::Item::Struct(it) => &it.ident,
        syn::Item::Union(it) => &it.ident,
        syn::Item::Trait(it) => &it.ident,
        syn::Item::TraitAlias(it) => &it.ident,
        syn::Item::Type(it) => &it.ident,
        syn::Item::ExternCrate(it) => it.rename.as_ref().map_or(&it.ident, |(_, rename)| rename),
        syn::Item::Use(it) => return use_binds(&it.tree, name),
        _ => return false,
    };
    unraw(ident) == name
}

/// Every name the items among `items` bind in the type namespace: a type, a
/// trait, a module, an `extern crate` or a non-glob `use`.
fn type_namespace_names<'ast>(items: impl Iterator<Item = &'ast syn::Item>) -> BTreeSet<String> {
    fn use_names(tree: &syn::UseTree, out: &mut BTreeSet<String>) {
        match tree {
            syn::UseTree::Path(path) => {
                if matches!(&*path.tree, syn::UseTree::Group(group)
                    if group.items.iter().any(|item| matches!(item,
                        syn::UseTree::Name(leaf) if leaf.ident == "self")))
                {
                    out.insert(unraw(&path.ident));
                }
                use_names(&path.tree, out);
            }
            syn::UseTree::Name(leaf) if leaf.ident != "self" => {
                out.insert(unraw(&leaf.ident));
            }
            syn::UseTree::Rename(rename) => {
                out.insert(unraw(&rename.rename));
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    use_names(item, out);
                }
            }
            syn::UseTree::Name(_) | syn::UseTree::Glob(_) => {}
        }
    }
    let mut out = BTreeSet::new();
    for item in items {
        let ident = match item {
            syn::Item::Mod(it) => &it.ident,
            syn::Item::Enum(it) => &it.ident,
            syn::Item::Struct(it) => &it.ident,
            syn::Item::Union(it) => &it.ident,
            syn::Item::Trait(it) => &it.ident,
            syn::Item::TraitAlias(it) => &it.ident,
            syn::Item::Type(it) => &it.ident,
            syn::Item::ExternCrate(it) => {
                it.rename.as_ref().map_or(&it.ident, |(_, rename)| rename)
            }
            syn::Item::Use(it) => {
                use_names(&it.tree, &mut out);
                continue;
            }
            _ => continue,
        };
        out.insert(unraw(ident));
    }
    out
}

/// Whether a `use` tree binds `name` (a glob binds nothing it shows).
fn use_binds(tree: &syn::UseTree, name: &str) -> bool {
    match tree {
        syn::UseTree::Path(path) => {
            // `use m::{self};` binds `m`.
            let binds_self = matches!(&*path.tree, syn::UseTree::Group(group)
                if group.items.iter().any(|item| matches!(item,
                    syn::UseTree::Name(leaf) if leaf.ident == "self")));
            (binds_self && unraw(&path.ident) == name) || use_binds(&path.tree, name)
        }
        syn::UseTree::Name(leaf) => unraw(&leaf.ident) == name,
        syn::UseTree::Rename(rename) => unraw(&rename.rename) == name,
        syn::UseTree::Group(group) => group.items.iter().any(|item| use_binds(item, name)),
        syn::UseTree::Glob(_) => false,
    }
}

fn is_punct(tree: &TokenTree, ch: char) -> bool {
    matches!(tree, TokenTree::Punct(punct) if punct.as_char() == ch)
}

/// Whether `tokens` hold the punctuation `ch` at any group depth.
fn contains_punct(tokens: TokenStream, ch: char) -> bool {
    tokens.into_iter().any(|tree| match tree {
        TokenTree::Group(group) => contains_punct(group.stream(), ch),
        tree => is_punct(&tree, ch),
    })
}

/// The path above each name a `use` tree imports without a glob, with the
/// name. A `self` leaf imports the module its path names, so it contributes
/// that module's own path and name.
fn named_leaves(
    tree: &syn::UseTree,
    prefix: &mut Vec<String>,
    out: &mut Vec<(Vec<String>, String)>,
) {
    match tree {
        syn::UseTree::Path(path) => {
            prefix.push(unraw(&path.ident));
            named_leaves(&path.tree, prefix, out);
            prefix.pop();
        }
        syn::UseTree::Group(group) => {
            for item in &group.items {
                named_leaves(item, prefix, out);
            }
        }
        syn::UseTree::Name(leaf) if leaf.ident == "self" => {
            if let Some((name, module)) = prefix.split_last() {
                out.push((module.to_vec(), name.clone()));
            }
        }
        syn::UseTree::Name(leaf) => out.push((prefix.clone(), unraw(&leaf.ident))),
        syn::UseTree::Rename(rename) => out.push((prefix.clone(), unraw(&rename.ident))),
        syn::UseTree::Glob(_) => {}
    }
}

/// The path above each glob in a `use` tree, from its root.
fn glob_prefixes(tree: &syn::UseTree, prefix: &mut Vec<String>, out: &mut Vec<Vec<String>>) {
    match tree {
        syn::UseTree::Path(path) => {
            prefix.push(unraw(&path.ident));
            glob_prefixes(&path.tree, prefix, out);
            prefix.pop();
        }
        syn::UseTree::Group(group) => {
            for item in &group.items {
                glob_prefixes(item, prefix, out);
            }
        }
        syn::UseTree::Glob(_) => out.push(prefix.clone()),
        syn::UseTree::Name(_) | syn::UseTree::Rename(_) => {}
    }
}

/// The names the `use` items among `items` import under their own name from a
/// path that starts at a std root (`Vec` in `use std::vec::Vec;`).
fn std_use_names<'ast>(items: impl Iterator<Item = &'ast syn::Item>) -> BTreeSet<String> {
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
                if prefix.first().is_some_and(|root| is_std_root(root)) {
                    out.insert(unraw(&leaf.ident));
                }
            }
            syn::UseTree::Rename(rename) => {
                if prefix.first().is_some_and(|root| is_std_root(root))
                    && rename.ident == rename.rename
                {
                    out.insert(unraw(&rename.rename));
                }
            }
            syn::UseTree::Glob(_) => {}
        }
    }
    let mut out = BTreeSet::new();
    for item in items {
        if let syn::Item::Use(it) = item {
            walk(&it.tree, &mut Vec::new(), &mut out);
        }
    }
    out
}

/// The tokens of `item` that READ type names: the whole item, except that the
/// name a type-namespace item declares is left out.
fn reading_tokens(item: &syn::Item) -> TokenStream {
    let mut item = item.clone();
    let placeholder = syn::Ident::new("__trust_vc_bound_name", proc_macro2::Span::call_site());
    match &mut item {
        syn::Item::Type(it) => it.ident = placeholder,
        syn::Item::Struct(it) => it.ident = placeholder,
        syn::Item::Enum(it) => it.ident = placeholder,
        syn::Item::Union(it) => it.ident = placeholder,
        syn::Item::Trait(it) => it.ident = placeholder,
        syn::Item::TraitAlias(it) => it.ident = placeholder,
        syn::Item::Mod(it) => it.ident = placeholder,
        // A `use` or `extern crate` item binds; its path is not a spelling of
        // a type this module reads.
        syn::Item::Use(_) | syn::Item::ExternCrate(_) => return TokenStream::new(),
        _ => {}
    }
    item.to_token_stream()
}

/// Whether a primitive type name `name` bound inside an inline module can be
/// what some spelling in the file denotes:
///
/// * a bare spelling of `name` (not after `::`) anywhere in that module's
///   items, other than the declared name of a binding item — a nested module
///   is included, although Rust does not let it see its parent's items;
/// * any glob `use` in the file, which may import the module's items; or
/// * a path anywhere in the file (including macro and attribute tokens) whose
///   last segment is `name` and whose first segment is neither `core` nor
///   `std`.
///
/// A binding only reachable through a `core::` / `std::` prefix is left to the
/// width lane's recorded residual for a captured prefix.
fn module_binding_is_reachable(
    name: &str,
    module_tokens: &TokenStream,
    has_glob_import: bool,
    file: Option<&File>,
    func: &ItemFn,
) -> bool {
    if has_glob_import || spells(module_tokens.clone(), name, Spelling::Bare) {
        return true;
    }
    let file_tokens = file.map_or_else(TokenStream::new, ToTokens::to_token_stream);
    spells(file_tokens, name, Spelling::QualifiedOutsideStd)
        || spells(func.to_token_stream(), name, Spelling::QualifiedOutsideStd)
}

#[derive(Clone, Copy)]
enum Spelling {
    /// An identifier not preceded by `::`.
    Bare,
    /// The last segment of a path of two or more segments whose first segment
    /// is neither `core` nor `std`.
    QualifiedOutsideStd,
}

/// Whether `tokens` (at any group depth) spell `name` the way `spelling` says.
fn spells(tokens: TokenStream, name: &str, spelling: Spelling) -> bool {
    let flat: Vec<TokenTree> = tokens.into_iter().collect();
    for (index, tree) in flat.iter().enumerate() {
        match tree {
            TokenTree::Group(group) => {
                if spells(group.stream(), name, spelling) {
                    return true;
                }
            }
            TokenTree::Ident(ident) if unraw(ident) == name => {
                let after_path_sep = index >= 2 && is_path_sep(&flat[index - 2], &flat[index - 1]);
                match spelling {
                    Spelling::Bare if !after_path_sep => return true,
                    Spelling::QualifiedOutsideStd
                        if after_path_sep && !path_starts_with_std(&flat[..index]) =>
                    {
                        return true;
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
    false
}

fn is_path_sep(first: &TokenTree, second: &TokenTree) -> bool {
    matches!(
        (first, second),
        (TokenTree::Punct(a), TokenTree::Punct(b))
            if a.as_char() == ':' && a.spacing() == Spacing::Joint && b.as_char() == ':'
    )
}

/// Whether the path that ends just after `before` starts at a `core` or `std`
/// segment (with or without a leading `::`). `before` holds every token up to
/// the path's last `::`.
fn path_starts_with_std(before: &[TokenTree]) -> bool {
    let mut end = before.len();
    loop {
        // `before[..end]` ends with `::`; step over it to the segment before.
        if end < 2 || !is_path_sep(&before[end - 2], &before[end - 1]) {
            return false;
        }
        end -= 2;
        let Some(TokenTree::Ident(segment)) = before.get(end.wrapping_sub(1)) else {
            return false;
        };
        let segment = unraw(segment);
        end -= 1;
        let continues = end >= 2 && is_path_sep(&before[end - 2], &before[end - 1]);
        if !continues {
            return segment == "core" || segment == "std";
        }
        // A leading `::` (nothing before it that is a segment) ends the path.
        let leading = end == 2 || !matches!(before.get(end - 3), Some(TokenTree::Ident(_)));
        if leading {
            return segment == "core" || segment == "std";
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn refusal(src: &str) -> Option<String> {
        let file = syn::parse_file(src).expect("fixture parses");
        let func = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "f" => Some(func.clone()),
                _ => None,
            })
            .expect("fixture has `fn f`");
        verified_refusal(Some(&file), &func)
    }

    #[test]
    fn each_rebinding_of_a_type_name_is_refused() {
        for src in [
            "type u64 = u8; fn f() {}",
            "#[allow(non_camel_case_types)] struct u8; fn f() {}",
            "mod u8 {} fn f() {}",
            "use core::primitive::u8 as u64; fn f() {}",
            "use core::primitive::u8 as Byte; fn f() {}",
            "use m::u64; mod m { pub type u64 = u8; } fn f() {}",
            "extern crate alloc as u64; fn f() {}",
            "fn f() { use core::primitive::u8 as u64; }",
            "fn f() { type u64 = u8; }",
            "fn g() { use core::primitive::u8 as u64; } fn f() {}",
            "type int = u8; fn f() {}",
            "struct nat(u8); fn f() {}",
            "use m::Foo as int; fn f() {}",
            "trait T { type u8; } fn f() {}",
            "fn f<u8>(x: u8) {}",
            "struct S; impl S { fn g<u64>(&self) {} } fn f() {}",
            "fn f<Vec>(x: Vec) {}",
            "fn f<int>(x: int) {}",
            "struct H<bool>(bool); fn f() {}",
            "mod m { pub type u64 = u8; pub fn g(a: u64) {} } fn f() {}",
            "mod m { pub type u64 = u8; } use m::*; fn f() {}",
            "mod m { pub type u64 = u8; } fn f(a: m::u64) {}",
            "mod m { pub type u64 = u8; } fn f() { let _ = crate::m::u64::MAX; }",
            // A std-meaning type name bound by the file.
            "struct Vec<T>(T); fn f() {}",
            "fn f() { struct Box<T>(T); }",
            "enum Rc { A } fn f() {}",
            "mod Vec {} fn f() {}",
            "trait Result {} fn f() {}",
            "use m::MyVec as Vec; fn f() {}",
            "type Vec<T> = m::MyVec<T>; fn f() {}",
            "use heapless::Vec; fn f() {}",
            "use std::collections::BTreeMap as HashMap; fn f() {}",
            "type Result<E, T> = std::result::Result<T, E>; fn f() {}",
            "type Vec<T> = std::vec::Vec<u8>; fn f() {}",
            "mod m { pub struct Vec<T>(T); impl<T> Vec<T> {} } fn f() {}",
            "mod m { pub struct Vec<T>(T); } use m::*; fn f() {}",
            // A std-meaning type name spelled outside the std roots.
            "fn f() { let v: heapless::Vec<u8, 2> = heapless::Vec::new(); }",
            "mod m; fn f(v: m::Vec<u32>) {}",
            "mod m { pub struct Vec<T>(T); } fn f(v: m::Vec<u32>) {}",
            "fn f(v: ::heapless::Vec<u8, 2>) {}",
            "fn f(v: crate::m::String) {}",
            "use crate::fmt; fn f() -> fmt::Result { Ok(()) }",
            "trait Tr { type String; fn g() -> Self::String; } fn f() {}",
            "enum Val { String(u64) } trait Tr { fn g(v: Self::String) {} } fn f() {}",
            "enum Val { String(u64) } impl Val { fn g(v: Self::String) {} } fn f() {}",
            "fn f() -> <u8 as Tr>::Vec {}",
            // A generic spelled like a name the file binds in the type
            // namespace, anywhere in the file.
            "struct T; fn f<T>(x: T) {}",
            "struct W; fn g<W>() {} fn f() {}",
            "struct W; struct H<W>(W); fn f() {}",
            "struct W; struct H<X>(X); impl<W> H<W> { fn s(&self, a: W) {} } fn f() {}",
            "enum E { A } fn g<E>() {} fn f() {}",
            "union U { a: u8 } fn f<U>() {}",
            "type W = u8; fn f<W>() {}",
            "trait Val {} fn f<Val>() {}",
            "trait Tr<W> {} struct W; fn f() {}",
            "mod m { pub struct W; } fn f<W>() {}",
            "fn g() { struct W; } fn f<W>() {}",
            "fn f<W>() { struct W; }",
            "use m::W; fn f<W>() {}",
            "use m::Other as W; fn f<W>() {}",
            "mod W {} fn f<W>() {}",
            "use std::fmt::Display; fn f<Display>() {}",
            "trait Tr { type Item; } fn f<Item>() {}",
            "struct S; impl Iterator for S { type Item = u8; fn next(&mut self) -> Option<u8> { None } } \
             fn f<Item>() {}",
            // A glob from outside the file, where a std name it can bind is
            // spelled.
            "use heapless::*; fn f() { let _v: Vec<u32, 1> = Vec::new(); }",
            "use ::heapless::*; fn f() -> String { String::new() }",
            "use crate::prelude::*; fn f() -> u8 { 1 } fn g() -> Result<u8, u8> { Ok(1) }",
            "use super::*; fn f(x: u8) { let _ = Some(x); }",
            "use other::*; fn f() {} fn g(x: u8) -> Option<u8> { None }",
            "use other::*; #[ensures(result == Some(1))] fn f() {}",
            "use other::*; fn f() -> u64 { Default::default() }",
            "use other::*; fn f(x: u64) { drop(x); }",
            "use a::{b, c::*}; fn f() -> Option<u8> { None }",
            "mod m; use m::*; fn f() -> Option<u8> { None }",
            "mod m { pub fn g() {} } use m::n::*; fn f() -> Option<u8> { None }",
            "mod m {} use crate::m::*; fn f() -> Option<u8> { None }",
            "extern crate heapless; use heapless::*; fn f() -> Option<u8> { None }",
            "use x::y as z; use z::*; fn f() -> Option<u8> { None }",
            "struct S; use S::*; fn f() -> Option<u8> { None }",
            // A module of that name exists, but not in the scope of the glob.
            "mod m { pub mod heapless {} } use heapless::*; fn f() -> Option<u8> { None }",
            "fn g() { mod inner {} } use inner::*; fn f() -> Option<u8> { None }",
            "mod m { fn g() -> Option<u8> { use super::super::*; None } } fn f() {}",
            // A glob in a block reaches that block, which a caller may read.
            "fn f() { use heapless::*; let _v: Vec<u32, 1> = Vec::new(); }",
            "fn g() { use heapless::*; let _v: Vec<u32, 1> = Vec::new(); } fn f() {}",
            "fn f() { let _ = || { use other::*; Some(1u8) }; }",
            // A glob in the tokens of a macro or an attribute.
            "fn f() { assert!({ use other::*; Some(1u8).is_some() }); }",
            "#[ensures({ use other::*; result == Some(1) })] fn f() {}",
            "macro_rules! m { () => { use $crate::*; } } fn f() -> Option<u8> { None }",
            "macro_rules! m { () => { use $crate::{a::*}; } } fn f() -> Option<u8> { None }",
            // A glob in a module reaches every scope that imports from it.
            "mod m { pub use heapless::*; } use m::*; \
             fn f() { let _v: Vec<u32, 1> = Vec::new(); }",
            "fn f() -> Option<u8> { mod inner { pub use other::*; } None }",
            // A std import wins only in the glob's own scope, and only at file
            // scope or in a block.
            "use heapless::*; use std::vec::Vec; fn f() -> Option<u8> { None }",
            "use std::vec::Vec; fn f() { use heapless::*; let _v: Vec<u32, 1> = Vec::new(); }",
            "mod m { pub use heapless::*; use std::vec::Vec; } use m::*; \
             fn f() { let _v: Vec<u32, 1> = Vec::new(); }",
            "use heapless::*; use std::collections::HashMap; fn f() -> Vec<u8> { Vec::new() }",
            // A glob from outside the file, where a primitive type name it can
            // bind is spelled.
            "mod other; use crate::other::*; fn f(a: u8) { let _y = (a as u64) / 2 + 200; }",
            "use other::*; fn f(x: u64) {}",
            "use other::*; fn f() { let _ = u32::MAX; }",
            "use other::*; fn f() -> bool { true }",
            "use other::*; fn f(s: &str) {}",
            "fn f() { use other::*; let _y: u64 = 1; }",
            "fn f() { let _ = || { use other::*; 1 as u64 }; }",
            "fn f() { assert!({ use other::*; 1 as u64 == 1 }); }",
            "mod m { pub use other::*; } use m::*; fn f(x: u64) {}",
            "use vstd::prelude::*; fn f(x: Seq<u8>) {}",
            "use heapless::*; use std::vec::Vec; fn f() -> Vec<u8> { Vec::new() }",
            "fn f() { use heapless::*; use std::vec::Vec; let _v: Vec<u8> = Vec::new(); }",
        ] {
            let refusal = refusal(src);
            assert!(
                refusal
                    .as_deref()
                    .is_some_and(|message| message.starts_with(TYPE_NAME_REBINDING_TAG)),
                "{src}: expected a refusal, got {refusal:?}"
            );
        }
    }

    #[test]
    fn ordinary_files_are_not_refused() {
        for src in [
            "fn f(x: u8) -> u64 { x as u64 }",
            "type Byte = u8; fn f(x: Byte) {}",
            "use std::collections::HashMap; fn f() {}",
            "use vstd::prelude::*; fn f() {}",
            "use trust_vc_types::{int, nat}; fn f(x: int) {}",
            "use trust_vc_types::int as int; fn f() {}",
            // A module or trait spelled like a ghost scalar is never a type.
            "mod real { pub trait Tr {} } fn f<T: real::Tr>(x: T) {}",
            "trait nat {} fn f() {}",
            "fn f<T: Copy>(x: T) {}",
            // Generics spelled unlike every type-namespace name of the file.
            "struct W; fn f<T>(x: T) {}",
            "struct W; trait Val {} fn f<T: Val>() -> W { W }",
            "use std::collections::HashMap; fn f<K, V>(m: HashMap<K, V>) {}",
            "enum E { A } struct H<T>(T); impl<T> H<T> { fn g(&self) {} } fn f() {}",
            "fn f<F: Fn(u64, u64) -> u64>(g: F) {}",
            "struct S<T>(T); impl<T> S<T> { fn g(&self) {} } fn f() {}",
            "fn f() { let v: Vec<::core::primitive::u8> = Vec::new(); }",
            // A module binding nothing in the file can reach.
            "mod primitive { pub type u64 = ::core::primitive::u32; } fn f(x: u64) {}",
            // The std types themselves, however they are imported or spelled.
            "use std::collections::{HashMap, HashSet}; fn f(m: HashMap<u8, u8>) {}",
            "use std::{collections::BTreeMap, fmt}; fn f() {}",
            "use alloc::vec::Vec; fn f(v: Vec<u8>) {}",
            "use std::vec::Vec as Vec; fn f() {}",
            "use std::fmt; struct P; impl fmt::Display for P { \
             fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { Ok(()) } } fn f() {}",
            "use std::fmt::{self, Display}; fn f() -> fmt::Result { Ok(()) }",
            "use std::io; fn f() -> io::Result<()> { Ok(()) }",
            "use std::fmt::Write as _; fn f() {}",
            "fn f() -> std::fmt::Result { Ok(()) }",
            "fn f(v: ::std::vec::Vec<u8>) {}",
            "fn f<'a>(v: &'a ::std::vec::Vec<u8>) {}",
            "fn f(v: &mut ::std::vec::Vec<u8>) {}",
            "fn f() { let m = std::collections::HashMap::<u8, u8>::new(); }",
            "fn f() -> ::std::vec::Vec<u8> { ::std::vec::Vec::new() }",
            "fn f(o: Option<u8>) -> Option<u8> { match o { \
             ::core::option::Option::Some(x) => ::core::option::Option::Some(x), \
             ::core::option::Option::None => ::core::option::Option::None } }",
            "fn f() -> Vec<::std::string::String> { Vec::new() }",
            // An alias naming the std type of its own name, parameters in order.
            "type Result<T> = std::result::Result<T, u8>; fn f() -> Result<u8> { Ok(1) }",
            "type Vec<T> = std::vec::Vec<T>; fn f(v: std::vec::Vec<u8>) {}",
            "type Result<T, E = u8> = core::result::Result<T, E>; fn f() {}",
            "type String = ::std::string::String; fn f() {}",
            // A variant of a file enum spelled like a std type.
            "enum Val { String(u64) } fn f(x: u64) -> Val { Val::String(x) }",
            "enum Val { String(u64) } impl Val { fn g(x: u64) -> Self { Self::String(x) } } \
             fn f() {}",
            // Read only by the interior-mutability classifier, which fails
            // closed on a type it does not know.
            "struct Cell(i32); fn f() {}",
            // A glob over std, or over an inline module or enum of the file.
            "use std::collections::*; fn f() -> Vec<u8> { Vec::new() }",
            "use ::core::option::*; fn f() -> Option<u8> { None }",
            "use alloc::vec::*; fn f() -> Vec<u8> { Vec::new() }",
            "mod m { pub fn g() {} } use m::*; fn f() -> Option<u8> { None }",
            "mod m { pub mod n {} } use self::m::n::*; fn f() -> Vec<u8> { Vec::new() }",
            "enum E { A, B } use E::*; fn f() -> Option<u8> { None }",
            "fn f() -> Option<u8> { mod m { pub fn g() {} } use m::*; None }",
            "mod a { pub fn g() {} mod b { use super::*; fn h() -> Option<u8> { None } } } \
             fn f() {}",
            "mod a { mod b { use super::super::*; fn h() -> Option<u8> { None } } } fn f() {}",
            "fn f() -> Option<u8> { use self::*; None }",
            "fn f() { assert!({ use std::collections::*; Vec::<u8>::new().is_empty() }); }",
            // A glob from outside the file whose reach spells no such name.
            "use vstd::prelude::*; struct S; fn f(x: Seq<S>) {}",
            "fn g() { use spec_use::*; concrete_b(1); } fn f() -> Option<u8> { None }",
            "fn g() { use other::*; h(); } fn f(x: u64) -> u64 { x }",
            "fn f() -> u64 { use other::*; 0 }",
            // A literal's suffix is not a path: `200u64` is the primitive.
            "use other::*; fn f() { let _x = 200u64; }",
            // A glob over std or over an inline module of the file, beside a
            // primitive spelling.
            "use std::collections::*; fn f(x: u64) -> bool { x > 0 }",
            "mod m { pub fn g() {} } use m::*; fn f(x: u64) -> bool { x > 0 }",
            // A std import in the glob's own scope wins over the glob there.
            "use heapless::*; use std::vec::Vec; fn f() -> Vec<()> { Vec::new() }",
            "use heapless::*; use std::{collections::HashMap, vec::Vec as Vec}; \
             fn f(m: HashMap<(), Vec<()>>) {}",
            "fn f() { use heapless::*; use std::vec::Vec; let _v: Vec<()> = Vec::new(); }",
        ] {
            assert_eq!(refusal(src), None, "{src}");
        }
    }

    #[test]
    fn a_name_read_from_another_declaration_is_refused() {
        for src in [
            // A declared type name bound to another item or from elsewhere.
            "mod a { pub type W = u64; } mod c { pub type V = u8; } use c::V as W; \
             fn f(v: W) {}",
            "mod a { pub type W = u64; } use other::W; fn f(v: W) {}",
            "mod a { pub type W = u64; } use crate::a::W; fn f(v: W) {}",
            "mod a { pub type W = u64; } use ::a::W; fn f(v: W) {}",
            "mod a { pub type W = u64; } mod b { pub use other::W; } use b::*; fn f(v: W) {}",
            "mod a { pub type W = u64; } fn f() { use other::W; let _v: W = 1; }",
            "type W = u64; mod m { use other::W; pub fn g(v: W) {} } fn f() {}",
            // Through a path that does not lead to the declaration.
            "mod a { pub type W = u64; } type V = other::W; fn f(v: V) {}",
            "mod a { pub type W = u64; } fn f(v: crate::a::W) {}",
            "mod a { pub type W = u64; } fn f(v: ::a::W) {}",
            "mod a { pub type W = u64; } mod b {} fn f(v: b::W) {}",
            "mod a { pub type W = u64; } trait Tr { type W; } fn f<T: Tr>(v: <T as Tr>::W) {}",
            "struct W; struct S; impl S { fn g() -> Self::W { W } } fn f() {}",
            // `Self::W` that need not be a variant: a type position, a trait
            // (whose supertrait can give an associated type `W`), an `impl`
            // of a type that is not an enum, or tokens that declare an item.
            "enum E { W } struct W; impl E { fn g(v: Self::W) {} } fn f() {}",
            "pub type Item = u64; pub enum K { Item } \
             trait Tr: Iterator<Item = u8> { fn h(v: Self::Item) {} } fn f() {}",
            "enum E { W } struct W; trait Tr { fn g() { let _x = Self::W; } } fn f() {}",
            "enum E { W } struct W; struct S; impl S { fn g() { let _x = Self::W; } } fn f() {}",
            "enum E { W } struct W; impl E { fn g() { m!(trait T { fn h(v: Self::W); }); } } \
             fn f() {}",
            // `E::W` is the associated type `W` where one is declared.
            "enum E { W } type W = u64; impl E { type W = u8; } fn f(v: E::W) {}",
            "enum Ordering { Less } fn f(a: u8) -> std::cmp::Ordering { a.cmp(&a) }",
            // `extern crate self as core;` leads `core::primitive::u8` to the
            // file's own `primitive::u8`.
            "extern crate self as core; pub mod primitive { pub type u8 = ::std::primitive::u64; } \
             fn f() { let _v: Vec<core::primitive::u8> = Vec::new(); }",
            "struct Cell { v: u8 } fn f(c: &std::cell::Cell<u8>) {}",
            "struct Default; fn f() -> u8 { std::default::Default::default() }",
            "mod a { pub type W = u64; } fn f() { assert!(other::W::MAX > 0); }",
            "mod a { pub type W = u64; } #[ensures(result == other::W::MAX)] fn f() -> u64 { 0 }",
            // A glob from outside the file reaches a bare spelling.
            "mod a { pub struct W; } use other::*; fn f(w: W) {}",
            "mod a { pub struct W; } fn f() { use other::*; let _w: Option<W> = None; }",
            // A ghost scalar from outside this toolchain's crates.
            "use other::*; fn f(x: int) {}",
            "fn f() { use crate::other::*; let _y: nat = 1; }",
            "use crate::m::int; fn f(x: int) {}",
            "use super::int; fn f(x: int) {}",
            "use other::int; mod m { use super::int; pub fn g(x: int) {} } fn f() {}",
        ] {
            let refusal = refusal(src);
            assert!(
                refusal
                    .as_deref()
                    .is_some_and(|message| message.starts_with(TYPE_NAME_REBINDING_TAG)),
                "{src}: expected a refusal, got {refusal:?}"
            );
        }
    }

    #[test]
    fn a_name_read_from_its_declaration_is_not_refused() {
        for src in [
            "mod a { pub type W = u64; } use a::W; fn f(v: W) {}",
            "use std::fmt; type Result<T> = std::result::Result<T, u8>; fn f(s: fmt::Result) {}",
            "mod a { pub type W = u64; } use self::a::W; fn f(v: W) {}",
            "mod a { pub type W = u64; } use a::W as W; fn f(v: W) {}",
            "mod a { pub type W = u64; } fn f(v: a::W) {}",
            "mod a { pub type W = u64; } fn f(v: self::a::W) {}",
            "type W = u64; mod m { use super::W; pub fn g(v: W) {} } fn f() {}",
            "mod a { pub type W = u64; } mod b { pub use super::a::W; } use b::W; fn f(v: W) {}",
            "mod a { pub type W = u64; } mod b { pub use super::a::W; } fn f(v: b::W) {}",
            "enum E { W } struct W; fn f() -> E { E::W }",
            "enum E { W } struct W; impl E { fn g() -> Self { Self::W } } fn f() {}",
            "enum E { W(u8) } struct W; impl E { fn g(e: Self) -> u8 { match e { Self::W(x) => x } } } \
             fn f() {}",
            "enum E { W } struct W; impl E { fn g(e: Self) -> bool { matches!(e, Self::W) } } \
             fn f() {}",
            "use other::*; struct W; fn f(w: W) {}",
            "use other::*; mod a { pub struct W; } use a::W; fn f(w: W) {}",
            "mod a { pub struct W; } use a::*; fn f(w: W) {}",
            "use trust_vc_types::int; mod m { use super::int; pub fn g(x: int) {} } fn f() {}",
            "use trust_vc_types::{int, nat}; fn f(x: int, y: nat) {}",
            "use vstd::prelude::*; fn f(x: int) {}",
            "use trust_vc_types::*; fn f(x: nat) {}",
        ] {
            assert_eq!(refusal(src), None, "{src}");
        }
    }

    #[test]
    fn without_a_file_the_function_itself_is_scanned() {
        let func: ItemFn = syn::parse_str("fn f<u8>(x: u8) {}").expect("parses");
        assert!(verified_refusal(None, &func).is_some());
        let func: ItemFn =
            syn::parse_str("fn f() { use core::primitive::u8 as u64; }").expect("parses");
        assert!(verified_refusal(None, &func).is_some());
        let func: ItemFn = syn::parse_str("fn f<T>() { struct T; }").expect("parses");
        assert!(verified_refusal(None, &func).is_some());
        let func: ItemFn = syn::parse_str("fn f<T>(x: T) {}").expect("parses");
        assert_eq!(verified_refusal(None, &func), None);
    }

    #[test]
    fn generic_names_are_collected_from_every_item() {
        let file = syn::parse_file(
            "struct S<A>(A); impl<B> S<B> { fn g<C>(&self) {} } trait T<D> {} fn f<E>() {}",
        )
        .expect("parses");
        let func = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) => Some(func.clone()),
                _ => None,
            })
            .expect("fixture has `fn f`");
        let names = generic_type_param_names(Some(&file), &func);
        assert_eq!(
            names.into_iter().collect::<Vec<_>>(),
            ["A", "B", "C", "D", "E"]
        );
    }
}
