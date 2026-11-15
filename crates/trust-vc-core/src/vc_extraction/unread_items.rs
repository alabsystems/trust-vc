// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Refuses a `Verified` answer for a function whose file can hold an impl, a
//! trait or a type this lane does not read.
//!
//! The lane reads a file as written, and takes the impls, traits and types the
//! text shows to be all there are. `==` on a struct with no `PartialEq` impl
//! in the text is read as structural equality, `x.clone()` on a `u64` as
//! `Clone::clone`, and `u64` as the primitive. An item the text does not show
//! breaks each of these readings:
//!
//! * a macro can emit one. With `macro_rules! peq { ($t:ty) => { impl
//!   PartialEq for $t { fn eq(&self, _: &Self) -> bool { false } } } }` and
//!   `peq!(P);`, `p == p` is false. A macro that declares `trait MyClone {
//!   fn clone(self) -> Self; }` with `impl MyClone for u64` makes `x.clone()`
//!   return what that impl returns, and one that expands to `type u64 = u8;`
//!   makes `u64` a byte. The invocation can sit anywhere, since an `impl`
//!   applies to the whole crate: in a statement of another function, or in an
//!   expression that expands to a block holding the `impl`;
//! * a derive or an attribute macro from another crate can emit any item;
//! * an `impl` or a `trait` written inside a function body or another block
//!   (`const _: () = { impl PartialEq for P { .. } };`) applies to the whole
//!   crate, while the lane reads impls and traits only at module level;
//! * `syn` leaves some items unparsed (a `macro` 2.0 definition, `impl
//!   const`), and the lane reads none of them.
//!
//! So a function is refused when its file holds any of these:
//!
//! * a macro invocation, in any position (an item, a statement, an
//!   expression, a type, a pattern, or the arguments of another macro or of an
//!   attribute), whose expansion can hold an item. Only these are read as
//!   holding none:
//!   - a std macro whose expansion is fixed ([`STD_ITEMLESS_MACROS`]), bare or
//!     under `std::` or `core::`;
//!   - a macro of this toolchain's own crates, bare ([`TOOLCHAIN_MACROS`]) or
//!     under one of [`TOOLCHAIN_ROOTS`], whose expansions do not declare items
//!     for user types;
//!   - a `macro_rules!` macro of the file whose every rule expands only to code
//!     without an item the lane misreads (see [`TokenScan::macro_rules_hazard`]),
//!     invoked with arguments that hold no item keyword where its rules expand
//!     them.
//!
//!   A bare name counts only where the file does not bind it to something
//!   else: a `use`, a `#[macro_use] extern crate`, or a glob whose source the
//!   file does not show (a glob cannot bind a std prelude macro name: that is
//!   an ambiguity error). The arguments of an admitted std or toolchain macro
//!   must not hold an `impl` or a `trait`, except the specifications of
//!   external items that [`SPEC_ITEM_MACROS`] take;
//! * a `derive` other than the nine the language defines;
//! * an attribute that can be a macro: anything but a built-in attribute
//!   ([`BUILTIN_ATTRIBUTES`]), a tool attribute (`rustfmt::`, `clippy::`,
//!   `diagnostic::`), or this toolchain's own (`trust_vc::…`, `verifier::…`,
//!   and the bare names the lane reads, [`toolchain_attribute`]);
//! * an `impl` or a `trait` inside a block, except an inherent impl of a type
//!   declared in that same block;
//! * a marker the `state_machine!` expansion left for an invocation that is not
//!   trust_vc's own `state_machine!`, or for an item it dropped;
//! * an item `syn` does not parse.
//!
//! A refutation and an earlier refusal are kept unchanged: neither can be a
//! false `Verified`.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::{Delimiter, Spacing, TokenStream, TokenTree};
use quote::ToTokens;
use syn::visit::Visit;
use syn::{File, ItemFn};

use crate::macro_scope::FileMacroScopes;

/// The tag every refusal from this module starts with.
pub(super) const UNREAD_ITEM_TAG: &str = "unread item";

/// Std macros whose expansion is fixed by std and declares no item. Their
/// arguments are read like any other tokens of the file.
///
/// Left out on purpose: `include!` (it pastes in another file), `thread_local!`
/// (it declares statics), and every macro that is not stable std surface.
const STD_ITEMLESS_MACROS: &[&str] = &[
    "addr_of",
    "addr_of_mut",
    "assert",
    "assert_eq",
    "assert_matches",
    "assert_ne",
    "cfg",
    "column",
    "compile_error",
    "concat",
    "dbg",
    "debug_assert",
    "debug_assert_eq",
    "debug_assert_matches",
    "debug_assert_ne",
    "env",
    "eprint",
    "eprintln",
    "file",
    "format",
    "format_args",
    "include_bytes",
    "include_str",
    "line",
    "matches",
    "module_path",
    "offset_of",
    "option_env",
    "panic",
    "pin",
    "print",
    "println",
    "stringify",
    "todo",
    "unimplemented",
    "unreachable",
    "vec",
    "write",
    "writeln",
];

/// The std macros of [`STD_ITEMLESS_MACROS`] that are in the prelude. A glob
/// import of one of these names makes a bare invocation ambiguous, a compile
/// error, so a glob cannot rebind it.
const STD_PRELUDE_MACROS: &[&str] = &[
    "assert",
    "assert_eq",
    "assert_ne",
    "cfg",
    "column",
    "compile_error",
    "concat",
    "dbg",
    "debug_assert",
    "debug_assert_eq",
    "debug_assert_ne",
    "env",
    "eprint",
    "eprintln",
    "file",
    "format",
    "format_args",
    "include_bytes",
    "include_str",
    "line",
    "matches",
    "module_path",
    "option_env",
    "panic",
    "print",
    "println",
    "stringify",
    "todo",
    "unimplemented",
    "unreachable",
    "vec",
    "write",
    "writeln",
];

/// The function-like macros of `trust_vc`, `trust_vc_types` and `vstd` that the
/// lane reads by their bare name. Each expands to proof code or to a value; it
/// declares no item for a user type.
const TOOLCHAIN_MACROS: &[&str] = &[
    "arbitrary",
    "assert",
    "assert_by",
    "assert_by_bit_vector",
    "assert_by_compute",
    "assert_by_contradiction",
    "assert_by_nonlinear",
    "assert_forall_by",
    "assert_maps_equal",
    "assert_multisets_equal",
    "assert_seqs_equal",
    "assert_sets_equal",
    "assert_with_proof",
    "assume",
    "assume_by",
    "broadcast_use",
    "calc",
    "choose",
    "cite",
    "closure",
    "decreases_by",
    "decreases_to",
    "ensures",
    "equal",
    "exists",
    "ext_eq",
    "ext_ne",
    "extern_spec",
    "external_spec",
    "forall",
    "ghost_ensures",
    "ghost_requires",
    "hide",
    "invariant",
    "invariant_except_break",
    "loop_decreases",
    "loop_ensures",
    "map",
    "old",
    "open_atomic_invariant",
    "open_atomic_invariant_in_proof",
    "open_local_invariant",
    "open_local_invariant_in_proof",
    "proof_block",
    "recommends",
    "recommends_by",
    "requires",
    "reveal",
    "reveal_group",
    "reveal_with_fuel",
    "seq",
    "set",
    "state_machine",
    "strict_eq",
    "tokenized_state_machine",
    "track_let",
    "trust_vc_assert",
    "trust_vc_assert_by",
    "trust_vc_assume",
    "trust_vc_broadcast_use",
    "trust_vc_hide",
    "trust_vc_invariant",
    "trust_vc_invariant_except_break",
    "trust_vc_loop_decreases",
    "trust_vc_loop_ensures",
    "trust_vc_proof_block",
    "trust_vc_reveal",
];

/// Toolchain macros whose arguments are a language of their own (the state
/// machine DSL, with its `transition!` and `init!` forms and its `fn` items).
/// Their arguments are not scanned.
const DSL_MACROS: &[&str] = &["state_machine", "tokenized_state_machine"];

/// Toolchain macros whose arguments are specifications of items outside the
/// file, which the lane reads: an `impl` there declares no impl.
const SPEC_ITEM_MACROS: &[&str] = &["extern_spec", "external_spec"];

/// Path roots whose macros are this toolchain's own.
const TOOLCHAIN_ROOTS: &[&str] = &["trust_vc", "trust_vc_types", "trust_mc", "vstd"];

/// Path roots whose macros are std's.
const STD_ROOTS: &[&str] = &["std", "core"];

/// The derives the language defines. Their expansion is an impl of that trait
/// for the annotated type, which the lane reads.
const BUILTIN_DERIVES: &[&str] = &[
    "Clone",
    "Copy",
    "Debug",
    "Default",
    "Eq",
    "Hash",
    "Ord",
    "PartialEq",
    "PartialOrd",
];

/// Attributes the compiler handles itself. None of them expands to an item.
/// `derive` and `cfg_attr` are read separately.
const BUILTIN_ATTRIBUTES: &[&str] = &[
    "allow",
    "automatically_derived",
    "cfg",
    "cold",
    "collapse_debuginfo",
    "crate_name",
    "crate_type",
    "debugger_visualizer",
    "deny",
    "deprecated",
    "doc",
    "expect",
    "export_name",
    "feature",
    "forbid",
    "global_allocator",
    "ignore",
    "inline",
    "instruction_set",
    "link",
    "link_name",
    "link_ordinal",
    "link_section",
    "macro_export",
    "macro_use",
    "must_use",
    "no_builtins",
    "no_link",
    "no_main",
    "no_mangle",
    "no_std",
    "non_exhaustive",
    "panic_handler",
    "path",
    "proc_macro",
    "proc_macro_attribute",
    "proc_macro_derive",
    "recursion_limit",
    "repr",
    "should_panic",
    "target_feature",
    "test",
    "track_caller",
    "type_length_limit",
    "used",
    "warn",
    "windows_subsystem",
];

/// Attribute namespaces that name no macro: the compiler's tool namespaces,
/// and this toolchain's own `trust_vc::` and `verifier::`.
const ATTRIBUTE_TOOL_ROOTS: &[&str] = &["clippy", "diagnostic", "rustfmt", "trust_vc", "verifier"];

/// Keywords that begin an item the lane misreads when it cannot see it: an
/// impl, a trait, a type or module binding, or a `macro` 2.0 definition. A
/// `macro_rules!` definition is not one: every definition in the file's
/// tokens, at any depth, is indexed and read where it is invoked.
const ITEM_KEYWORDS: &[&str] = &["extern", "impl", "macro", "mod", "trait", "type", "use"];

/// Keywords that declare a named item whose name alone decides whether an
/// unseen copy of it can change how the lane reads the file.
const DECLARING_KEYWORDS: &[&str] = &["const", "enum", "fn", "static", "struct", "union"];

/// Keywords whose item applies outside the block that holds it.
const CRATE_WIDE_ITEM_KEYWORDS: &[&str] = &["impl", "trait"];

/// `macro_rules!` fragment kinds that pass their tokens through unparsed, so
/// that they can combine with the tokens around them into a macro invocation
/// or an item the arguments do not show.
const RAW_FRAGMENT_KINDS: &[&str] = &["item", "meta", "stmt", "tt"];

/// Rust's keywords. An ident followed by `!` and a group is a macro invocation
/// unless it is one of these (`if !(a) { .. }`).
const KEYWORDS: &[&str] = &[
    "Self", "abstract", "as", "async", "await", "become", "box", "break", "const", "continue",
    "crate", "do", "dyn", "else", "enum", "extern", "false", "final", "fn", "for", "gen", "if",
    "impl", "in", "let", "loop", "macro", "match", "mod", "move", "mut", "override", "priv", "pub",
    "ref", "return", "self", "static", "struct", "super", "trait", "true", "try", "type", "typeof",
    "unsafe", "unsized", "use", "virtual", "where", "while", "yield",
];

/// The refusal message for a `Verified` answer of `func`, or `None` when its
/// file shows every impl, trait and type it holds. Without a file, `func`
/// alone is read. See the module documentation.
pub(super) fn verified_refusal(file: Option<&File>, func: &ItemFn) -> Option<String> {
    let hazard = match file {
        Some(file) => file_hazard(file),
        None => file_hazard(&File {
            shebang: None,
            attrs: Vec::new(),
            items: vec![syn::Item::Fn(func.clone())],
        }),
    }?;
    Some(format!(
        "{UNREAD_ITEM_TAG}: {hazard}, so this file can hold an impl, a trait or a type this lane \
         does not read. A `Verified` answer is refused; a refutation would be kept"
    ))
}

/// Why `file` can hold an item the lane does not read, or `None`.
pub(super) fn file_hazard(file: &File) -> Option<String> {
    hazard(file, false)
}

/// [`file_hazard`] for a file of a crate whose type items the crate lane
/// copies into another file. A macro whose expansion declares a `struct`, an
/// `enum` or a `union` counts whatever its name: one file not binding that
/// name says nothing of the files the copied items reach (`pub struct W(pub
/// u8);` from `mk!();` in `c.rs` is the `W` that `use c::W;` imports, beside
/// the `pub type W = u64;` of `a.rs` the lane copies).
pub(super) fn crate_file_hazard(file: &File) -> Option<String> {
    hazard(file, true)
}

fn hazard(file: &File, any_declared_type: bool) -> Option<String> {
    let mut facts = FactScan::default();
    facts.visit_file(file);
    let FactScan {
        mut facts,
        hazard,
        blocks: _,
    } = facts;
    index_macro_rules(file.to_token_stream(), &mut facts.macro_rules);
    if let Some(hazard) = hazard {
        return Some(hazard);
    }
    let (toolchain_globs, opaque_globs): (Vec<String>, Vec<String>) =
        super::type_name_rebinding::opaque_glob_renderings(file)
            .into_iter()
            .partition(|rendered| {
                let root = rendered.trim_start_matches("::");
                let root = root.split("::").next().unwrap_or_default().trim();
                TOOLCHAIN_ROOTS.contains(&root)
            });
    let scan = TokenScan {
        facts: &facts,
        scopes: FileMacroScopes::from_file(file),
        opaque_glob: opaque_globs.into_iter().next(),
        toolchain_glob: !toolchain_globs.is_empty(),
        any_declared_type,
        macro_verdicts: RefCell::new(BTreeMap::new()),
    };
    scan.stream(file.to_token_stream(), Place::PARSED)
}

/// What the syntax tree of a file says about its bindings.
#[derive(Default)]
struct FileFacts {
    /// The rule bodies of every `macro_rules!` definition in the file's
    /// tokens, by macro name: at any depth, and inside the arguments or the
    /// rules of another macro.
    macro_rules: BTreeMap<String, Vec<TokenStream>>,
    /// For every name a `use` or an `extern crate` binds, at any depth, the
    /// first segments of the paths it is bound from.
    use_roots: BTreeMap<String, BTreeSet<String>>,
    /// Every name the file binds as an item or an import, at any depth.
    bound_names: BTreeSet<String>,
    /// Every name the file declares as an item (not an import), at any depth.
    item_names: BTreeSet<String>,
    /// Every inline module of the file, at any depth.
    inline_mods: BTreeSet<String>,
}

impl FileFacts {
    /// True when the file binds `root` to something other than the crate of
    /// that name: an item, or an import of another path under that name
    /// (`use other as trust_vc;`, `mod verifier {}`).
    fn rebinds_root(&self, root: &str) -> bool {
        self.item_names.contains(root)
            || self
                .use_roots
                .get(root)
                .is_some_and(|found| found.iter().any(|source| source != root))
    }

    /// True when some `use` binds `name` from a path whose first segment is
    /// not one of `roots`.
    fn imports_from_outside(&self, name: &str, roots: &[&str]) -> bool {
        self.use_roots
            .get(name)
            .is_some_and(|found| found.iter().any(|root| !roots.contains(&root.as_str())))
    }

    /// True when some `use` can bind the macro name `name` to a macro that is
    /// neither the file's own `macro_rules!` of that name nor a std or
    /// toolchain macro: its path starts somewhere other than the name itself
    /// (`use assume;` re-exports the file's macro), `self`, an inline module
    /// of the file, or a std or toolchain crate.
    fn imports_macro_from_elsewhere(&self, name: &str) -> bool {
        self.use_roots.get(name).is_some_and(|found| {
            found.iter().any(|root| {
                root != name
                    && root != "self"
                    && !self.inline_mods.contains(root)
                    && !TOOLCHAIN_ROOTS.contains(&root.as_str())
                    && !STD_ROOTS.contains(&root.as_str())
                    && root != "alloc"
            })
        })
    }

    /// True when `root::…::name!` can name the file's own `macro_rules!` macro
    /// `name`: a bare name, a path through `crate`, `self`, `super` or
    /// `$crate`, or one through an inline module of the file.
    fn names_file_macro(&self, root: Option<&str>, name: &str) -> bool {
        self.macro_rules.contains_key(name)
            && match root {
                None | Some("crate" | "self" | "super" | "$crate") => true,
                Some(root) => self.inline_mods.contains(root),
            }
    }
}

/// Collects [`FileFacts`] and the first hazard the syntax tree itself shows.
#[derive(Default)]
struct FactScan {
    facts: FileFacts,
    hazard: Option<String>,
    /// For each block the walk is inside, innermost last, the structs, enums
    /// and unions written directly in it.
    blocks: Vec<BTreeSet<String>>,
}

impl FactScan {
    fn flag(&mut self, hazard: String) {
        if self.hazard.is_none() {
            self.hazard = Some(hazard);
        }
    }

    fn bind(&mut self, ident: &syn::Ident) {
        self.facts.bound_names.insert(unraw(ident));
        self.facts.item_names.insert(unraw(ident));
    }

    fn use_tree(&mut self, tree: &syn::UseTree, root: Option<&str>) {
        match tree {
            syn::UseTree::Path(path) => {
                let first = unraw(&path.ident);
                self.use_tree(&path.tree, Some(root.unwrap_or(&first)));
            }
            syn::UseTree::Name(name) => {
                let bound = unraw(&name.ident);
                let root = root.map_or_else(|| bound.clone(), str::to_string);
                self.record_use(bound, root);
            }
            syn::UseTree::Rename(rename) => {
                let root = root.map_or_else(|| unraw(&rename.ident), str::to_string);
                self.record_use(unraw(&rename.rename), root);
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    self.use_tree(item, root);
                }
            }
            syn::UseTree::Glob(_) => {}
        }
    }

    fn record_use(&mut self, bound: String, root: String) {
        self.facts.bound_names.insert(bound.clone());
        self.facts.use_roots.entry(bound).or_default().insert(root);
    }
}

impl<'ast> Visit<'ast> for FactScan {
    fn visit_block(&mut self, block: &'ast syn::Block) {
        let local_types = block
            .stmts
            .iter()
            .filter_map(|stmt| match stmt {
                syn::Stmt::Item(syn::Item::Struct(item)) => Some(unraw(&item.ident)),
                syn::Stmt::Item(syn::Item::Enum(item)) => Some(unraw(&item.ident)),
                syn::Stmt::Item(syn::Item::Union(item)) => Some(unraw(&item.ident)),
                _ => None,
            })
            .collect();
        self.blocks.push(local_types);
        syn::visit::visit_block(self, block);
        self.blocks.pop();
    }

    fn visit_item(&mut self, item: &'ast syn::Item) {
        if let syn::Item::Verbatim(tokens) = item {
            self.flag(format!(
                "the file holds an item this lane does not parse (`{}`)",
                abbreviate(tokens)
            ));
        }
        syn::visit::visit_item(self, item);
    }

    fn visit_impl_item(&mut self, item: &'ast syn::ImplItem) {
        if let syn::ImplItem::Verbatim(tokens) = item {
            self.flag(format!(
                "the file holds an impl item this lane does not parse (`{}`)",
                abbreviate(tokens)
            ));
        }
        syn::visit::visit_impl_item(self, item);
    }

    fn visit_trait_item(&mut self, item: &'ast syn::TraitItem) {
        if let syn::TraitItem::Verbatim(tokens) = item {
            self.flag(format!(
                "the file holds a trait item this lane does not parse (`{}`)",
                abbreviate(tokens)
            ));
        }
        syn::visit::visit_trait_item(self, item);
    }

    fn visit_foreign_item(&mut self, item: &'ast syn::ForeignItem) {
        if let syn::ForeignItem::Verbatim(tokens) = item {
            self.flag(format!(
                "the file holds a foreign item this lane does not parse (`{}`)",
                abbreviate(tokens)
            ));
        }
        syn::visit::visit_foreign_item(self, item);
    }

    /// An `impl` in a block applies wherever its type is visible. An inherent
    /// impl of a type written in the same block reaches only that block's
    /// values, through methods nothing else can name, so it is the one kind
    /// that is not a hazard.
    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        if let Some(local_types) = self.blocks.last() {
            let block_local_inherent = item.trait_.is_none()
                && matches!(item.self_ty.as_ref(), syn::Type::Path(path)
                    if path.qself.is_none()
                        && path.path.leading_colon.is_none()
                        && path.path.segments.len() == 1
                        && local_types.contains(&unraw(&path.path.segments[0].ident)));
            if !block_local_inherent {
                self.flag("the file writes an `impl` inside a block".to_string());
            }
        }
        syn::visit::visit_item_impl(self, item);
    }

    fn visit_item_trait(&mut self, item: &'ast syn::ItemTrait) {
        if !self.blocks.is_empty() {
            self.flag("the file writes a `trait` inside a block".to_string());
        }
        self.bind(&item.ident);
        syn::visit::visit_item_trait(self, item);
    }

    fn visit_item_trait_alias(&mut self, item: &'ast syn::ItemTraitAlias) {
        if !self.blocks.is_empty() {
            self.flag("the file writes a trait alias inside a block".to_string());
        }
        self.bind(&item.ident);
        syn::visit::visit_item_trait_alias(self, item);
    }

    fn visit_item_extern_crate(&mut self, item: &'ast syn::ItemExternCrate) {
        if item
            .attrs
            .iter()
            .any(|attr| attr.path().is_ident("macro_use"))
        {
            self.flag(format!(
                "the file writes `#[macro_use] extern crate {};`, which can bind any macro name",
                item.ident
            ));
        }
        let root = unraw(&item.ident);
        let bound = item
            .rename
            .as_ref()
            .map_or_else(|| root.clone(), |(_, rename)| unraw(rename));
        self.record_use(bound, root);
        syn::visit::visit_item_extern_crate(self, item);
    }

    fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
        self.use_tree(&item.tree, None);
        syn::visit::visit_item_use(self, item);
    }

    fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
        self.bind(&item.ident);
        syn::visit::visit_item_struct(self, item);
    }

    fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
        self.bind(&item.ident);
        syn::visit::visit_item_enum(self, item);
    }

    fn visit_item_union(&mut self, item: &'ast syn::ItemUnion) {
        self.bind(&item.ident);
        syn::visit::visit_item_union(self, item);
    }

    fn visit_item_type(&mut self, item: &'ast syn::ItemType) {
        self.bind(&item.ident);
        syn::visit::visit_item_type(self, item);
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        self.bind(&item.sig.ident);
        syn::visit::visit_item_fn(self, item);
    }

    fn visit_item_const(&mut self, item: &'ast syn::ItemConst) {
        self.bind(&item.ident);
        syn::visit::visit_item_const(self, item);
    }

    fn visit_item_static(&mut self, item: &'ast syn::ItemStatic) {
        self.bind(&item.ident);
        syn::visit::visit_item_static(self, item);
    }

    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        self.bind(&item.ident);
        if item.content.is_some() {
            self.facts.inline_mods.insert(unraw(&item.ident));
        }
        syn::visit::visit_item_mod(self, item);
    }
}

/// Where tokens sit, and so what in them needs reading.
#[derive(Clone, Copy)]
struct Place {
    /// The tokens are the arguments of a macro or an attribute, which `syn`
    /// leaves unparsed. An `impl` or a `trait` there is not seen by the
    /// syntax-tree walk.
    unparsed: bool,
    /// An `impl` or a `trait` here is one the lane reads: the arguments of
    /// [`SPEC_ITEM_MACROS`].
    items_read: bool,
    /// Inner attributes here are attributes of the code, not the syntax of a
    /// toolchain macro (a quantifier's `#![auto]` or `#![trigger f(x)]`). An
    /// inner attribute inside a block cannot be a macro on stable Rust, and a
    /// toolchain macro reads its own; outer attributes are read everywhere.
    inner_attributes: bool,
}

impl Place {
    const PARSED: Place = Place {
        unparsed: false,
        items_read: false,
        inner_attributes: true,
    };
}

/// Walks a file's tokens for macro invocations and attributes.
struct TokenScan<'a> {
    facts: &'a FileFacts,
    scopes: FileMacroScopes,
    /// A glob `use` whose source the file does not show and that is not over a
    /// toolchain crate. It can bind any bare macro name.
    opaque_glob: Option<String>,
    /// The file has a glob `use` over a toolchain crate, which brings the
    /// toolchain's macros into that module.
    toolchain_glob: bool,
    /// A `struct`, `enum` or `union` a macro declares is a hazard whatever its
    /// name ([`crate_file_hazard`]).
    any_declared_type: bool,
    /// The verdict on each `macro_rules!` name, once decided.
    macro_verdicts: RefCell<BTreeMap<String, Option<String>>>,
}

impl TokenScan<'_> {
    /// The first hazard in `tokens`.
    fn stream(&self, tokens: TokenStream, place: Place) -> Option<String> {
        let trees: Vec<TokenTree> = tokens.into_iter().collect();
        let mut index = 0;
        while index < trees.len() {
            if let Some((content, next, inner)) = attribute_at(&trees, index) {
                if !inner || place.inner_attributes {
                    if let Some(hazard) = self.attribute(content.clone()) {
                        return Some(hazard);
                    }
                }
                let args = Place {
                    unparsed: true,
                    ..place
                };
                if let Some(hazard) = self.stream(content, args) {
                    return Some(hazard);
                }
                index = next;
                continue;
            }
            if is_macro_rules_definition(&trees, index) {
                // The rules are read where the macro is invoked.
                index += 4;
                continue;
            }
            match &trees[index] {
                TokenTree::Ident(ident) if begins_invocation(&trees, index) => {
                    let name = unraw(ident);
                    let root = path_root(&trees[..index]);
                    let Some(TokenTree::Group(args)) = trees.get(index + 2) else {
                        unreachable!("an invocation ends in a group");
                    };
                    if let Some(hazard) = self.invocation(root.as_deref(), &name, &args.stream()) {
                        return Some(hazard);
                    }
                    let file_macro = self.facts.names_file_macro(root.as_deref(), &name);
                    let toolchain = !file_macro
                        && match root.as_deref() {
                            None | Some("crate" | "self") => {
                                TOOLCHAIN_MACROS.contains(&name.as_str())
                                    && !STD_ITEMLESS_MACROS.contains(&name.as_str())
                            }
                            Some(root) => TOOLCHAIN_ROOTS.contains(&root),
                        };
                    let args_read = if file_macro {
                        self.forwards_arguments(&name)
                    } else {
                        !(toolchain && DSL_MACROS.contains(&name.as_str()))
                    };
                    if args_read {
                        let args_place = Place {
                            unparsed: true,
                            items_read: place.items_read
                                || (toolchain && SPEC_ITEM_MACROS.contains(&name.as_str())),
                            inner_attributes: place.inner_attributes && !toolchain,
                        };
                        if let Some(hazard) = self.stream(args.stream(), args_place) {
                            return Some(hazard);
                        }
                    }
                    index += 3;
                    continue;
                }
                TokenTree::Ident(ident)
                    if place.unparsed
                        && !place.items_read
                        && CRATE_WIDE_ITEM_KEYWORDS.contains(&unraw(ident).as_str()) =>
                {
                    return Some(format!(
                        "the file writes `{ident}` in the arguments of a macro or an attribute"
                    ));
                }
                TokenTree::Group(group) => {
                    if let Some(hazard) = self.stream(group.stream(), place) {
                        return Some(hazard);
                    }
                }
                _ => {}
            }
            index += 1;
        }
        None
    }

    /// The hazard of an invocation of `root::…::name!(args)` written in the
    /// file, or `None` when its expansion holds no item.
    fn invocation(&self, root: Option<&str>, name: &str, args: &TokenStream) -> Option<String> {
        let spelled = match root {
            Some(root) => format!("{root}::…::{name}!"),
            None => format!("{name}!"),
        };
        if self.facts.names_file_macro(root, name) {
            return self.file_macro_invocation(name, args);
        }
        if root.is_none() && name == crate::state_machine_dsl::REFUSED_MARKER_MACRO {
            return self.refusal_marker(args);
        }
        self.named_macro_hazard(root, name)
            .map(|why| format!("the file invokes `{spelled}`, {why}"))
    }

    /// Why `root::…::name!`, which is not a macro of the file, can expand to
    /// an item, or `None` when it names a std or toolchain macro whose
    /// expansion holds none.
    ///
    /// A bare name, or one under `crate::` or `self::`, names that macro only
    /// where the file binds the name to nothing else. A glob whose source the
    /// file does not show can bind it too, except a std prelude macro: a glob
    /// import of that name is an ambiguity error, not a rebinding.
    fn named_macro_hazard(&self, root: Option<&str>, name: &str) -> Option<String> {
        let root = root.map(|root| if root == "$crate" { "crate" } else { root });
        let admitted = match root {
            None | Some("crate" | "self") => {
                (STD_ITEMLESS_MACROS.contains(&name) || TOOLCHAIN_MACROS.contains(&name))
                    && self.scopes.names_well_known(root, name)
            }
            Some(root) if STD_ROOTS.contains(&root) => {
                STD_ITEMLESS_MACROS.contains(&name)
                    && self.scopes.names_well_known(Some(root), name)
            }
            Some(root) if TOOLCHAIN_ROOTS.contains(&root) => {
                self.scopes.names_well_known(Some(root), name)
            }
            Some(_) => false,
        };
        if !admitted {
            return Some("a macro whose expansion this lane does not read".to_string());
        }
        // `crate::name!` and `self::name!` name what that module binds, which
        // is the toolchain's macro only when the file imports it from there.
        let imported_here = match root {
            Some("crate" | "self") => {
                self.toolchain_glob
                    || self.facts.use_roots.get(name).is_some_and(|roots| {
                        roots.iter().all(|root| {
                            TOOLCHAIN_ROOTS.contains(&root.as_str())
                                || STD_ROOTS.contains(&root.as_str())
                        })
                    })
            }
            _ => true,
        };
        if !imported_here {
            return Some(
                "a name the file does not import from a std or toolchain crate".to_string(),
            );
        }
        let glob_can_bind = match root {
            None => !STD_PRELUDE_MACROS.contains(&name),
            Some("crate" | "self") => true,
            Some(_) => false,
        };
        match &self.opaque_glob {
            Some(glob) if glob_can_bind => Some(format!("a name the glob `use {glob};` can bind")),
            _ => None,
        }
    }

    /// The hazard of a marker the `state_machine!` expansion left in place of
    /// an item it refused. The item is not read, so a marker that stands for a
    /// macro other than trust_vc's `state_machine!`, or for an item the
    /// expansion dropped, is a hazard; one for trust_vc's own refused machine
    /// or for a reference site is not. A marker name the file itself imports
    /// or can take from a glob is not the lane's marker.
    fn refusal_marker(&self, args: &TokenStream) -> Option<String> {
        let name = crate::state_machine_dsl::REFUSED_MARKER_MACRO;
        if self.facts.imports_from_outside(name, &[]) || self.opaque_glob.is_some() {
            return Some(format!(
                "the file invokes `{name}!`, a reserved name it binds to another macro"
            ));
        }
        let unread = args.clone().into_iter().any(|tree| {
            matches!(tree, TokenTree::Ident(ident)
                if ident == crate::state_machine_dsl::UNREAD_MARKER_FLAG)
        });
        unread.then(|| {
            "the file holds an item macro this lane does not expand (a `state_machine!` that is \
             not trust_vc's, or an item that did not parse back after rewriting)"
                .to_string()
        })
    }

    /// The hazard of invoking the file's own `macro_rules!` macro `name` with
    /// `args`.
    fn file_macro_invocation(&self, name: &str, args: &TokenStream) -> Option<String> {
        if self.facts.imports_macro_from_elsewhere(name) {
            return Some(format!(
                "the file invokes `{name}!`, a name it both defines and imports"
            ));
        }
        if let Some(glob) = &self.opaque_glob {
            return Some(format!(
                "the file invokes `{name}!` where the glob `use {glob};` can bind that name"
            ));
        }
        let forwarded = self.forwards_arguments(name);
        if let Some(keyword) = forwarded
            .then(|| first_ident_among(args, &[ITEM_KEYWORDS, DECLARING_KEYWORDS]))
            .flatten()
        {
            return Some(format!(
                "the file passes `{keyword}` to its macro `{name}!`, which can expand it to an item"
            ));
        }
        let why = self.macro_rules_hazard(name, &mut BTreeSet::new())?;
        Some(format!("the file invokes its macro `{name}!`, {why}"))
    }

    /// Whether some rule of the file's `macro_rules!` macro `name` expands a
    /// fragment, so that tokens of an invocation's arguments reach the
    /// expansion. A macro whose rules cannot be read counts as forwarding.
    fn forwards_arguments(&self, name: &str) -> bool {
        self.facts.macro_rules.get(name).is_some_and(|bodies| {
            bodies.iter().any(|body| match macro_rules_rules(body) {
                Some(rules) => rules.into_iter().any(|(_, transcriber)| {
                    let mut used = BTreeSet::new();
                    fragment_uses(transcriber, &mut used);
                    used.iter().any(|name| name != "crate")
                }),
                None => true,
            })
        })
    }

    /// Why an expansion of the file's `macro_rules!` macro `name` can hold an
    /// item the lane misreads, or `None`. `active` holds the macros whose rules
    /// are being read, so a recursive macro is read once.
    ///
    /// A rule's expansion is its transcriber, with each fragment replaced by
    /// tokens of the arguments. Parsed fragments (`expr`, `ty`, `pat`, `path`,
    /// `block`, `literal`, `lifetime`, `vis`, `ident`) are replaced by one
    /// token or one parsed node, which cannot combine with its neighbours into
    /// a new invocation; the raw kinds in [`RAW_FRAGMENT_KINDS`] can, so a
    /// macro that takes one is not read. With those out, the expansion holds
    /// an item only where the transcriber, or an argument, spells its keyword,
    /// and a nested invocation only where the transcriber spells it. The
    /// arguments are checked at each invocation, and the transcriber here: it
    /// must hold no keyword of [`ITEM_KEYWORDS`], declare only items whose
    /// name is literal and neither bound elsewhere in the file nor one the lane
    /// gives a meaning, name no macro by a fragment (`$m!()`), carry only
    /// attributes that are not macros, and invoke only macros that pass the
    /// same checks.
    fn macro_rules_hazard(&self, name: &str, active: &mut BTreeSet<String>) -> Option<String> {
        if let Some(verdict) = self.macro_verdicts.borrow().get(name) {
            return verdict.clone();
        }
        if !active.insert(name.to_string()) {
            return None;
        }
        let verdict = self.macro_rules_verdict(name, active);
        active.remove(name);
        self.macro_verdicts
            .borrow_mut()
            .insert(name.to_string(), verdict.clone());
        verdict
    }

    fn macro_rules_verdict(&self, name: &str, active: &mut BTreeSet<String>) -> Option<String> {
        let bodies = self.facts.macro_rules.get(name)?;
        for body in bodies {
            let Some(rules) = macro_rules_rules(body) else {
                return Some("whose rules this lane cannot read".to_string());
            };
            for (matcher, transcriber) in rules {
                let mut kinds = BTreeMap::new();
                fragment_kinds(matcher, &mut kinds);
                let mut used = BTreeSet::new();
                fragment_uses(transcriber.clone(), &mut used);
                for name in used.iter().filter(|name| name.as_str() != "crate") {
                    match kinds.get(name) {
                        Some(kind) if RAW_FRAGMENT_KINDS.contains(&kind.as_str()) => {
                            return Some(format!("which expands a `{kind}` fragment"));
                        }
                        Some(_) => {}
                        // A fragment of an enclosing macro, pasted in when
                        // this definition was expanded.
                        None => {
                            return Some(format!(
                                "which expands `${name}`, a fragment its own rules do not declare"
                            ));
                        }
                    }
                }
                if let Some(why) = self.transcriber_hazard(transcriber, active) {
                    return Some(why);
                }
            }
        }
        None
    }

    fn transcriber_hazard(
        &self,
        tokens: TokenStream,
        active: &mut BTreeSet<String>,
    ) -> Option<String> {
        let trees: Vec<TokenTree> = tokens.into_iter().collect();
        let mut index = 0;
        while index < trees.len() {
            if is_macro_rules_definition(&trees, index) {
                // Indexed with the file's macros and read where it is invoked.
                index += 4;
                continue;
            }
            if let Some((content, next, _)) = attribute_at(&trees, index) {
                if let Some(hazard) = self.attribute(content.clone()) {
                    return Some(format!("which can expand to an attribute: {hazard}"));
                }
                if let Some(why) = self.transcriber_hazard(content, active) {
                    return Some(why);
                }
                index = next;
                continue;
            }
            match &trees[index] {
                TokenTree::Punct(dollar) if dollar.as_char() == '$' => {
                    if let Some(TokenTree::Ident(_)) = trees.get(index + 1) {
                        if is_alone_bang(trees.get(index + 2)) {
                            return Some(
                                "which invokes a macro named by one of its arguments".to_string(),
                            );
                        }
                        index += 2;
                        continue;
                    }
                }
                TokenTree::Ident(ident) => {
                    let word = unraw(ident);
                    if ITEM_KEYWORDS.contains(&word.as_str()) {
                        return Some(format!("which can expand to `{word}`"));
                    }
                    if DECLARING_KEYWORDS.contains(&word.as_str()) {
                        if let Some(why) = self.declared_item_hazard(&trees, index) {
                            return Some(why);
                        }
                    }
                    if begins_invocation(&trees, index) {
                        let root = path_root(&trees[..index]);
                        let Some(TokenTree::Group(args)) = trees.get(index + 2) else {
                            unreachable!("an invocation ends in a group");
                        };
                        if let Some(why) =
                            self.nested_invocation_hazard(root.as_deref(), &word, active)
                        {
                            return Some(why);
                        }
                        if let Some(why) = self.transcriber_hazard(args.stream(), active) {
                            return Some(why);
                        }
                        index += 3;
                        continue;
                    }
                }
                TokenTree::Group(group) => {
                    if let Some(why) = self.transcriber_hazard(group.stream(), active) {
                        return Some(why);
                    }
                }
                _ => {}
            }
            index += 1;
        }
        None
    }

    /// The hazard of the item a transcriber declares with the keyword at
    /// `trees[index]`, or `None` when the keyword declares nothing there (a
    /// `fn(u64)` pointer type, `*const T`, `'static`) or declares an item no
    /// reading of the file can confuse with another.
    fn declared_item_hazard(&self, trees: &[TokenTree], index: usize) -> Option<String> {
        let TokenTree::Ident(keyword) = &trees[index] else {
            return None;
        };
        let keyword = unraw(keyword);
        if index > 0 {
            match &trees[index - 1] {
                TokenTree::Punct(p) if matches!(p.as_char(), '*' | '\'') => return None,
                TokenTree::Ident(raw) if raw == "raw" => return None,
                _ => {}
            }
        }
        let mut next = index + 1;
        if keyword == "static" || keyword == "const" {
            if let Some(TokenTree::Ident(word)) = trees.get(next) {
                if word == "mut" || word == "fn" || word == "unsafe" || word == "async" {
                    next += 1;
                }
            }
        }
        match trees.get(next) {
            Some(TokenTree::Punct(dollar)) if dollar.as_char() == '$' => Some(format!(
                "which declares a `{keyword}` item named by one of its arguments"
            )),
            Some(TokenTree::Ident(name)) => {
                let name = unraw(name);
                if name == "_" || name == "fn" {
                    return None;
                }
                if self.any_declared_type && matches!(keyword.as_str(), "struct" | "enum" | "union")
                {
                    return Some(format!(
                        "which declares the type `{name}`, a name another file of the crate can \
                         spell"
                    ));
                }
                if super::type_name_rebinding::is_lane_read_name(&name) {
                    return Some(format!(
                        "which declares `{name}`, a name this lane gives a meaning"
                    ));
                }
                if self.facts.bound_names.contains(&name) {
                    return Some(format!(
                        "which declares `{name}`, a name the file also binds"
                    ));
                }
                None
            }
            _ => None,
        }
    }

    /// The hazard of an invocation of `root::…::name!` inside a transcriber.
    fn nested_invocation_hazard(
        &self,
        root: Option<&str>,
        name: &str,
        active: &mut BTreeSet<String>,
    ) -> Option<String> {
        if self.facts.names_file_macro(root, name) {
            if self.facts.imports_macro_from_elsewhere(name) {
                return Some(format!(
                    "which invokes `{name}!`, a name the file both defines and imports"
                ));
            }
            return self
                .macro_rules_hazard(name, active)
                .map(|why| format!("which invokes `{name}!`, {why}"));
        }
        if DSL_MACROS.contains(&name) {
            return Some(format!("which invokes `{name}!`"));
        }
        self.named_macro_hazard(root, name)
            .map(|why| format!("which invokes `{name}!`, {why}"))
    }

    /// The hazard of the attribute whose bracketed content is `content`, or
    /// `None` when it cannot be a macro.
    fn attribute(&self, content: TokenStream) -> Option<String> {
        let trees: Vec<TokenTree> = content.into_iter().collect();
        let (path, leading_colon, rest) = attribute_path(&trees);
        let spelled = path.join("::");
        let Some(first) = path.first() else {
            return Some("the file carries an attribute this lane cannot read".to_string());
        };
        if leading_colon && (path.len() < 2 || !ATTRIBUTE_TOOL_ROOTS.contains(&first.as_str())) {
            return Some(format!(
                "the file carries the attribute `#[::{spelled}]`, which can be a macro"
            ));
        }
        if path.len() > 1 {
            if ATTRIBUTE_TOOL_ROOTS.contains(&first.as_str()) && !self.facts.rebinds_root(first) {
                return None;
            }
            return Some(format!(
                "the file carries the attribute `#[{spelled}]`, which can be a macro"
            ));
        }
        let args = rest.first();
        match first.as_str() {
            "derive" => self.derive(args),
            "cfg_attr" => self.cfg_attr(args),
            // `#[unsafe(no_mangle)]`: the attribute is the one inside.
            "unsafe" => match args {
                Some(TokenTree::Group(inner)) => self.attribute(inner.stream()),
                _ => Some("the file carries an `unsafe` attribute this lane cannot read".into()),
            },
            name if BUILTIN_ATTRIBUTES.contains(&name) => None,
            name if toolchain_attribute(name)
                && !self.facts.imports_from_outside(name, TOOLCHAIN_ROOTS) =>
            {
                self.opaque_glob.as_ref().map(|glob| {
                    format!(
                        "the file carries the attribute `#[{name}]` where the glob `use {glob};` \
                         can bind that name"
                    )
                })
            }
            name => Some(format!(
                "the file carries the attribute `#[{name}]`, which can be a macro"
            )),
        }
    }

    /// The hazard of `#[derive(args)]`.
    fn derive(&self, args: Option<&TokenTree>) -> Option<String> {
        let Some(TokenTree::Group(args)) = args else {
            return Some("the file carries a `derive` this lane cannot read".to_string());
        };
        for part in split_top_level_commas(args.stream()) {
            let (path, leading_colon, rest) = attribute_path(&part);
            let admitted = !leading_colon
                && rest.is_empty()
                && path.last().is_some_and(|name| {
                    BUILTIN_DERIVES.contains(&name.as_str())
                        && match path.len() {
                            1 => !self
                                .facts
                                .imports_from_outside(name, &["std", "core", "alloc"]),
                            _ => {
                                STD_ROOTS.contains(&path[0].as_str())
                                    && !self.facts.rebinds_root(&path[0])
                            }
                        }
                });
            if !admitted {
                return Some(format!(
                    "the file derives `{}`, a derive macro whose expansion this lane does not read",
                    path.join("::")
                ));
            }
        }
        None
    }

    /// The hazard of `#[cfg_attr(predicate, attributes..)]`: each attribute
    /// it may apply is read as if written directly.
    fn cfg_attr(&self, args: Option<&TokenTree>) -> Option<String> {
        let Some(TokenTree::Group(args)) = args else {
            return Some("the file carries a `cfg_attr` this lane cannot read".to_string());
        };
        split_top_level_commas(args.stream())
            .into_iter()
            .skip(1)
            .find_map(|attribute| self.attribute(attribute.into_iter().collect()))
    }
}

/// True for a bare attribute name that this toolchain's own crates or the
/// lane's desugarings define.
fn toolchain_attribute(name: &str) -> bool {
    super::attr_extract::KNOWN_TRUST_VC_ATTRIBUTES.contains(&name)
        || TOOLCHAIN_MACROS.contains(&name)
        || matches!(
            name,
            "cite" | "ghost_ensures" | "ghost_requires" | "inductive" | "invariant" | "sharding"
        )
        || name.starts_with("__trust_vc_")
}

/// The bracketed content of an attribute that starts at `trees[index]`, the
/// index after it, and whether it is an inner attribute: `#[..]` or `#![..]`.
fn attribute_at(trees: &[TokenTree], index: usize) -> Option<(TokenStream, usize, bool)> {
    let TokenTree::Punct(hash) = &trees[index] else {
        return None;
    };
    if hash.as_char() != '#' {
        return None;
    }
    let (bracket, next, inner) = match trees.get(index + 1) {
        Some(TokenTree::Punct(bang)) if bang.as_char() == '!' => {
            (trees.get(index + 2), index + 3, true)
        }
        other => (other, index + 2, false),
    };
    match bracket {
        Some(TokenTree::Group(group)) if group.delimiter() == Delimiter::Bracket => {
            Some((group.stream(), next, inner))
        }
        _ => None,
    }
}

/// The path at the start of an attribute's content, whether it has a leading
/// `::`, and the tokens after it.
fn attribute_path(trees: &[TokenTree]) -> (Vec<String>, bool, &[TokenTree]) {
    let mut index = 0;
    let leading_colon = is_path_separator(trees, 0);
    if leading_colon {
        index = 2;
    }
    let mut path = Vec::new();
    while let Some(TokenTree::Ident(segment)) = trees.get(index) {
        path.push(unraw(segment));
        index += 1;
        if is_path_separator(trees, index) {
            index += 2;
        } else {
            break;
        }
    }
    (path, leading_colon, &trees[index.min(trees.len())..])
}

fn is_path_separator(trees: &[TokenTree], index: usize) -> bool {
    matches!(
        (trees.get(index), trees.get(index + 1)),
        (Some(TokenTree::Punct(a)), Some(TokenTree::Punct(b)))
            if a.as_char() == ':' && a.spacing() == Spacing::Joint && b.as_char() == ':'
    )
}

/// Record every `macro_rules! name { .. }` in `tokens`, at any depth.
fn index_macro_rules(tokens: TokenStream, index: &mut BTreeMap<String, Vec<TokenStream>>) {
    let trees: Vec<TokenTree> = tokens.into_iter().collect();
    for (at, tree) in trees.iter().enumerate() {
        if is_macro_rules_definition(&trees, at) {
            if let (Some(TokenTree::Ident(name)), Some(TokenTree::Group(body))) =
                (trees.get(at + 2), trees.get(at + 3))
            {
                index.entry(unraw(name)).or_default().push(body.stream());
            }
        }
        if let TokenTree::Group(group) = tree {
            index_macro_rules(group.stream(), index);
        }
    }
}

/// True when `trees[index]` begins `macro_rules! name { .. }`.
fn is_macro_rules_definition(trees: &[TokenTree], index: usize) -> bool {
    matches!(
        (trees.get(index), trees.get(index + 1), trees.get(index + 2), trees.get(index + 3)),
        (
            Some(TokenTree::Ident(keyword)),
            Some(TokenTree::Punct(bang)),
            Some(TokenTree::Ident(_)),
            Some(TokenTree::Group(_)),
        ) if keyword == "macro_rules" && bang.as_char() == '!'
    )
}

/// True when `trees[index]` is the name of a macro invocation `name!(..)`: an
/// ident that is not a keyword, followed by an alone `!` and a group. `a != b`
/// carries a joint `!`.
fn begins_invocation(trees: &[TokenTree], index: usize) -> bool {
    let Some(TokenTree::Ident(ident)) = trees.get(index) else {
        return false;
    };
    if KEYWORDS.contains(&ident.to_string().as_str()) {
        return false;
    }
    if index > 0 {
        if let TokenTree::Punct(dollar) = &trees[index - 1] {
            if dollar.as_char() == '$' {
                return false;
            }
        }
    }
    is_alone_bang(trees.get(index + 1)) && matches!(trees.get(index + 2), Some(TokenTree::Group(_)))
}

fn is_alone_bang(tree: Option<&TokenTree>) -> bool {
    matches!(tree, Some(TokenTree::Punct(bang)) if bang.as_char() == '!' && bang.spacing() == Spacing::Alone)
}

/// The first segment of the path that ends right before `before`'s end:
/// `a::b::` answers `Some("a")`, `$crate::` answers `Some("$crate")`, and no
/// path answers `None`.
fn path_root(before: &[TokenTree]) -> Option<String> {
    let mut end = before.len();
    let mut root = None;
    while end >= 2 && is_path_separator(before, end - 2) {
        match before.get(end.wrapping_sub(3)) {
            Some(TokenTree::Ident(segment)) if end >= 3 => {
                let segment = unraw(segment);
                end -= 3;
                let crate_var = end >= 1
                    && matches!(&before[end - 1], TokenTree::Punct(p) if p.as_char() == '$');
                if crate_var {
                    return Some(format!("${segment}"));
                }
                root = Some(segment);
            }
            // A leading `::`: the root is the segment after it.
            _ => break,
        }
    }
    root
}

/// The rules of a `macro_rules!` body: each matcher and its transcriber.
fn macro_rules_rules(body: &TokenStream) -> Option<Vec<(TokenStream, TokenStream)>> {
    let trees: Vec<TokenTree> = body.clone().into_iter().collect();
    let mut rules = Vec::new();
    let mut index = 0;
    while index < trees.len() {
        let TokenTree::Group(matcher) = &trees[index] else {
            return None;
        };
        let arrow = matches!(
            (trees.get(index + 1), trees.get(index + 2)),
            (Some(TokenTree::Punct(eq)), Some(TokenTree::Punct(gt)))
                if eq.as_char() == '=' && eq.spacing() == Spacing::Joint && gt.as_char() == '>'
        );
        let Some(TokenTree::Group(transcriber)) = trees.get(index + 3) else {
            return None;
        };
        if !arrow {
            return None;
        }
        rules.push((matcher.stream(), transcriber.stream()));
        index += 4;
        if let Some(TokenTree::Punct(semi)) = trees.get(index) {
            if semi.as_char() == ';' {
                index += 1;
            }
        }
    }
    Some(rules)
}

/// Every `$name:kind` fragment declared in a matcher, at any depth.
fn fragment_kinds(matcher: TokenStream, kinds: &mut BTreeMap<String, String>) {
    let trees: Vec<TokenTree> = matcher.into_iter().collect();
    for (index, tree) in trees.iter().enumerate() {
        match tree {
            TokenTree::Group(group) => fragment_kinds(group.stream(), kinds),
            TokenTree::Punct(dollar) if dollar.as_char() == '$' => {
                if let (
                    Some(TokenTree::Ident(name)),
                    Some(TokenTree::Punct(colon)),
                    Some(TokenTree::Ident(kind)),
                ) = (
                    trees.get(index + 1),
                    trees.get(index + 2),
                    trees.get(index + 3),
                ) {
                    if colon.as_char() == ':' {
                        kinds.insert(unraw(name), unraw(kind));
                    }
                }
            }
            _ => {}
        }
    }
}

/// Every fragment a transcriber expands (`$name`), at any depth. A
/// `macro_rules!` definition inside it is left out: it is read on its own
/// where it is invoked, and a fragment it expands that its own rules do not
/// declare is a hazard there.
fn fragment_uses(transcriber: TokenStream, used: &mut BTreeSet<String>) {
    let trees: Vec<TokenTree> = transcriber.into_iter().collect();
    let mut index = 0;
    while index < trees.len() {
        if is_macro_rules_definition(&trees, index) {
            index += 4;
            continue;
        }
        match &trees[index] {
            TokenTree::Group(group) => fragment_uses(group.stream(), used),
            TokenTree::Punct(dollar) if dollar.as_char() == '$' => {
                if let Some(TokenTree::Ident(name)) = trees.get(index + 1) {
                    used.insert(unraw(name));
                }
            }
            _ => {}
        }
        index += 1;
    }
}

/// The first ident in `tokens`, at any depth, that is one of `sets`. The name
/// of a lifetime (`'static`) is not an ident here.
fn first_ident_among(tokens: &TokenStream, sets: &[&[&str]]) -> Option<String> {
    let trees: Vec<TokenTree> = tokens.clone().into_iter().collect();
    trees
        .iter()
        .enumerate()
        .find_map(|(index, tree)| match tree {
            TokenTree::Ident(ident) => {
                let lifetime = index > 0
                    && matches!(&trees[index - 1], TokenTree::Punct(p) if p.as_char() == '\'');
                let word = unraw(ident);
                (!lifetime && sets.iter().any(|set| set.contains(&word.as_str()))).then_some(word)
            }
            TokenTree::Group(group) => first_ident_among(&group.stream(), sets),
            _ => None,
        })
}

/// `tokens` split at its top-level commas, with empty parts dropped.
fn split_top_level_commas(tokens: TokenStream) -> Vec<Vec<TokenTree>> {
    let mut parts = vec![Vec::new()];
    for tree in tokens {
        match &tree {
            TokenTree::Punct(comma) if comma.as_char() == ',' => parts.push(Vec::new()),
            _ => parts.last_mut().expect("parts is never empty").push(tree),
        }
    }
    parts.retain(|part| !part.is_empty());
    parts
}

fn unraw(ident: &proc_macro2::Ident) -> String {
    syn::ext::IdentExt::unraw(ident).to_string()
}

/// The first few tokens of `tokens`, for a message.
fn abbreviate(tokens: &TokenStream) -> String {
    let text = tokens.to_string();
    match text.char_indices().nth(60) {
        Some((cut, _)) => format!("{} …", &text[..cut]),
        None => text,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hazard(src: &str) -> Option<String> {
        file_hazard(&syn::parse_file(src).expect("fixture parses"))
    }

    #[test]
    fn a_file_that_can_hold_an_unread_item_is_refused() {
        for src in [
            // A macro that emits an impl, at item, statement and expression
            // position.
            "macro_rules! m { ($t:ty) => { impl PartialEq for $t { fn eq(&self, _: &Self) -> bool { false } } } } struct P; m!(P); fn f() {}",
            "macro_rules! m { ($t:ty) => { impl PartialEq for $t { fn eq(&self, _: &Self) -> bool { false } } } } struct P; fn g() { m!(P); } fn f() {}",
            "macro_rules! m { ($t:ty) => {{ impl PartialEq for $t { fn eq(&self, _: &Self) -> bool { false } } 0u64 }} } struct P; fn g() -> u64 { m!(P) } fn f() {}",
            "mod inner { macro_rules! m { () => { impl S { fn v(&self) -> u64 { 2 } } } } struct S; m!(); } fn f() {}",
            // A macro that declares a trait, a type or an import.
            "macro_rules! m { () => { trait MyClone { fn clone(self) -> Self; } } } m!(); fn f() {}",
            "macro_rules! d { () => { type u64 = u8; } } d!(); fn f() {}",
            "macro_rules! d { () => { use core::primitive::u8 as u64; } } d!(); fn f() {}",
            "macro_rules! alias { ($n:ident, $t:ty) => { type $n = $t; } } alias!(u64, u8); fn f() {}",
            // A macro whose declared item's name is an argument, a name the
            // lane reads, or a name the file binds elsewhere.
            "macro_rules! s { ($n:ident) => { struct $n(u8); } } s!(u8); fn f() {}",
            "macro_rules! s { () => { struct u8(u64); } } s!(); fn f() {}",
            "macro_rules! s { () => { fn drop<T>(_: T) {} } } s!(); fn f() {}",
            "macro_rules! s { () => { const None: Option<u64> = Some(1); } } s!(); fn f() {}",
            "fn helper() -> u64 { 1 } mod m { macro_rules! s { () => { fn helper() -> u64 { 7 } } } s!(); } fn f() {}",
            // An item keyword in the arguments of the file's macro.
            "macro_rules! id { ($e:expr) => { $e } } fn g() -> u64 { id!({ impl Tr for u64 {} 0 }) } fn f() {}",
            "macro_rules! id { ($e:expr) => { $e } } fn g() -> u64 { id!({ struct Q; 0 }) } fn f() {}",
            // A raw fragment, a macro named by a fragment, a nested invocation
            // of an unknown macro.
            "macro_rules! m { ($($t:tt)*) => { $($t)* } } fn g() { m!(x); } fn f() {}",
            "macro_rules! m { ($i:item) => { $i } } m!(struct Q;); fn f() {}",
            "macro_rules! m { ($n:ident) => { $n!() } } fn g() { m!(other); } fn f() {}",
            "macro_rules! m { () => { other!() } } fn g() { m!(); } fn f() {}",
            "macro_rules! m { () => { crate::other!() } } fn g() { m!(); } fn f() {}",
            "macro_rules! a { () => { b!() } } macro_rules! b { () => { impl Tr for u8 {} } } fn g() { a!(); } fn f() {}",
            "macro_rules! m { () => { #[my_attr] fn q() {} } } m!(); fn f() {}",
            // A macro the file does not define, in any position.
            "peq!(P); fn f() {}",
            "fn g() { other::peq!(P); } fn f() {}",
            "fn g() -> u64 { let x = mk!(); x } fn f() {}",
            "fn g(x: mk!()) {} fn f() {}",
            "struct S; impl S { mk!(); } fn f() {}",
            "trait T { mk!(); } fn f() {}",
            "fn g() { assert!(mk!()); } fn f() {}",
            "#[trust_vc::requires(mk!())] fn g() {} fn f() {}",
            "fn g() { include!(\"x.rs\"); } fn f() {}",
            "fn g() { std::include!(\"x.rs\"); } fn f() {}",
            "thread_local! { static X: u8 = 0; } fn f() {}",
            "fn g() { crate::m!(); } fn f() {}",
            "fn g() { alloc::vec![1]; } fn f() {}",
            // A well-known name the file binds to something else.
            "use my_macros::assert; fn g() { assert!(true); } fn f() {}",
            "#[macro_use] extern crate other; fn f() {}",
            "mod trust_vc {} fn g() { trust_vc::assert!(true); } fn f() {}",
            "macro_rules! m { () => { 1 } } use other::m; fn g() -> u64 { m!() } fn f() {}",
            "macro_rules! x { () => { 1 } } mod m { pub use other::x; } fn g() -> u64 { m::x!() } fn f() {}",
            // An impl or a trait in a block, or in the arguments of an
            // admitted macro.
            "struct W; fn g() { impl PartialEq for W { fn eq(&self, _: &Self) -> bool { false } } } fn f() {}",
            "struct C; const _: () = { impl PartialEq for C { fn eq(&self, _: &Self) -> bool { false } } }; fn f() {}",
            "fn g() { trait MyClone { fn clone(self) -> Self; } } fn f() {}",
            "fn g() { mod m { impl Tr for u8 {} } } fn f() {}",
            "struct P; fn g() { struct Local; impl P { fn v(&self) -> u64 { 2 } } } fn f() {}",
            "fn g() { struct Local; impl PartialEq for Local { fn eq(&self, _: &Self) -> bool { false } } } fn f() {}",
            // A glob can bind a toolchain macro name, or a name under `crate::`.
            "use other::*; fn g() { invariant!(true); } fn f() {}",
            "use other::*; fn g() { crate::assert!(true); } fn f() {}",
            "fn g() { super::seq![1]; } fn f() {}",
            "fn g() { crate::seq![1]; } fn f() {}",
            "fn g() { self::vec![1]; } fn f() {}",
            // An outer attribute in a toolchain macro's arguments is read.
            "fn g() { trust_vc::proof_block!({ #[derive(MyEq)] struct Q; }); } fn f() {}",
            // Arguments a file macro forwards are read.
            "macro_rules! id { ($e:expr) => { $e }; } fn g() -> u64 { id!(other!()) } fn f() {}",
            // An impl in the arguments of a toolchain macro that re-emits them.
            "struct A; fn g() { trust_vc::proof_block!({ impl PartialEq for A { fn eq(&self, _: &Self) -> bool { false } } }); } fn f() {}",
            "mod trust_vc {} #[::trust_vc::ensures(true)] fn f() {}",
            "fn g() { let c = || { impl Tr for u8 {} }; } fn f() {}",
            // A macro defined by another macro's expansion, whose body the
            // outer macro fills.
            "macro_rules! outer { ($t:ty) => { macro_rules! inner { () => { impl Tr for $t {} } } }; } outer!(u8); inner!(); fn f() {}",
            "macro_rules! outer { ($e:expr) => { macro_rules! inner { () => { $e } } }; } outer!(1); fn g() -> u64 { inner!() } fn f() {}",
            "macro_rules! outer { ($($b:tt)*) => { macro_rules! inner { () => { $($b)* } } }; } outer!(impl Tr for u8 {}); inner!(); fn f() {}",
            "struct A; fn g() { assert!({ impl PartialEq for A { fn eq(&self, _: &Self) -> bool { false } } true }); } fn f() {}",
            // A derive or an attribute that can be a macro.
            "#[derive(MyEq)] struct P; fn f() {}",
            "#[derive(PartialEq, hjd::Hijack)] struct P; fn f() {}",
            "use my::PartialEq; #[derive(PartialEq)] struct P; fn f() {}",
            "#[derive(::core::cmp::PartialEq)] struct P; fn f() {}",
            "#[cfg_attr(test, derive(MyEq))] struct P; fn f() {}",
            "#[my_attr] struct P; fn f() {}",
            "#[some_crate::widget] fn g() {} fn f() {}",
            "#[tokio::test] fn g() {} fn f() {}",
            "#[post(result == 1)] fn g() {} fn f() {}",
            "use my::ensures; #[ensures(true)] fn g() {} fn f() {}",
            "struct P { #[my_field_attr] a: u8 } fn f() {}",
            "fn f() { #[my_attr] let x = 1; }",
            "#![my_inner] fn f() {}",
            "#[unsafe(my_attr)] fn g() {} fn f() {}",
            "mod trust_vc {} #[trust_vc::spec] fn g() {} fn f() {}",
            // An item syn does not parse.
            "pub macro m() {} fn f() {}",
            // A bare toolchain attribute a glob can bind.
            "use other::*; #[ensures(true)] fn g() {} fn f() {}",
            // A `state_machine!` marker for a foreign macro or a dropped item,
            // and a marker name the file imports.
            "__trust_vc_state_machine_refused! { 0 3 \"state_machine! `W`: via `o::state_machine`\" unread } fn f() {}",
            "use other::__trust_vc_state_machine_refused; __trust_vc_state_machine_refused! { 0 3 \"m\" } fn f() {}",
        ] {
            assert!(hazard(src).is_some(), "not refused: {src}");
        }
    }

    #[test]
    fn a_file_that_shows_every_item_is_not_refused() {
        for src in [
            "fn f() {}",
            "#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)] struct P { a: u64 } fn f() {}",
            "#[derive(std::fmt::Debug, core::clone::Clone)] struct P; fn f() {}",
            "#[cfg_attr(test, derive(Debug))] #[allow(dead_code)] struct P; fn f() {}",
            "#![allow(unused)] #![feature(let_chains)] #[inline] #[must_use] fn g() -> u8 { 0 } fn f() {}",
            "#[test] #[ignore] #[should_panic] fn g() {} #[cfg(test)] mod tests {} fn f() {}",
            "#[rustfmt::skip] #[clippy::msrv = \"1.70\"] fn g() {} fn f() {}",
            "#[unsafe(no_mangle)] pub extern \"C\" fn g() {} fn f() {}",
            "/// doc\n#[doc = \"x\"] fn f() {}",
            "#[trust_vc::requires(x > 0u64)] #[trust_vc::ensures(result > 0u64)] fn f(x: u64) -> u64 { x }",
            "#[requires(x > 0u64)] #[ensures(result > 0u64)] #[verifier(external_body)] #[verifier::rlimit(10)] fn f(x: u64) -> u64 { x }",
            "use trust_vc::ensures; #[ensures(true)] fn f() {}",
            "fn f(#[trust_vc::proof] x: u64) {}",
            // Admitted std and toolchain macros, in any position.
            "fn f(x: u64) { assert!(x == x); assert_eq!(x, x); debug_assert!(x >= 0); let v = vec![1u64]; println!(\"{}\", x); let s = format!(\"{x}\"); if !matches!(Some(x), Some(_)) { unreachable!() } }",
            "fn f() { std::assert!(true); core::panic!(\"x\"); }",
            "fn f() { trust_vc::assert!(true); trust_vc::invariant!(true); invariant!(true); assume!(true); let s = trust_vc_types::seq![1, 2]; let t = seq![1]; }",
            "fn f() { trust_vc::reveal_with_fuel!(g, 2); trust_vc::decreases_by!(g); open_atomic_invariant!(x => i => {}); }",
            "fn f() { trust_vc::assert!(matches!(Some(1u8), Some(_))); }",
            "use std::ptr::addr_of; fn f(x: u8) { let _p = addr_of!(x); }",
            "use super::*; fn f() {}",
            "use std::collections::*; fn f() { assert!(true); }",
            "use trust_vc::*; fn f() { assert!(true); }",
            // `if !(..)` and `a != b` are not invocations.
            "fn f(a: bool, b: u8) { if !(a) { return; } while !(a) {} let c = b != 0; let d = match !(a) { _ => 0 }; }",
            // Impls and traits at module level, and items in blocks that
            // stay in the block.
            "struct P; impl PartialEq for P { fn eq(&self, _: &Self) -> bool { true } } trait T {} mod m { impl super::T for u8 {} } fn f() {}",
            "fn f() { struct Local; fn helper() -> u64 { 1 } let x = helper(); }",
            "fn f() -> u64 { struct Local; impl Local { fn value() -> u64 { 11 } } Local::value() }",
            // A glob cannot rebind a std prelude macro; one over a toolchain
            // crate brings the toolchain's own.
            "use heapless::*; fn f(x: u64) { assert!(x == x); println!(\"{}\", x); }",
            "use trust_vc::*; use vstd::prelude::*; fn f() { invariant!(true); let s = crate::seq![1]; }",
            "use trust_vc_types::seq; fn f() { let s = crate::seq![1]; }",
            // A toolchain macro's own syntax, and its specifications of items
            // outside the file.
            "fn f() { trust_vc::assert_forall_by!(assert forall |k: int| #![autos] k == k by {}); }",
            "fn f() { trust_vc::assert!(forall(|x: int| #[trigger] g(x) >= 0)); }",
            "trust_vc::external_spec! { impl u8 { #[ensures(result == 0u8)] fn default() -> u8; } } fn f() {}",
            "#[::trust_vc::ensures(true)] fn f() {}",
            // The file's own macros whose expansion holds no item the lane
            // misreads.
            "macro_rules! nothing { () => {}; } nothing!(); fn f() {}",
            "fn f() { let mut x = 1; macro_rules! add_1 { () => { x = x + 1; }; } add_1!(); trust_vc::assert!(x == 2); }",
            "fn f() { macro_rules! with { ($s1:expr) => {{ let s1 = $s1; trust_vc::assert!(s1); }}; } with!(true); }",
            "fn f() { macro_rules! grp { () => { trust_vc::broadcast_use!(g); }; } grp!(); }",
            "macro_rules! double { ($e:expr) => { $e * 2 } } fn g(x: u64) -> u64 { double!(x) } fn f() {}",
            "macro_rules! twice { ($e:expr) => { double!(double!($e)) } } macro_rules! double { ($e:expr) => { $e * 2 } } fn g(x: u64) -> u64 { twice!(x) } fn f() {}",
            "macro_rules! count { () => { 0usize }; ($x:expr $(, $rest:expr)*) => { 1usize + count!($($rest),*) }; } fn g() -> usize { count!(1, 2, 3) } fn f() {}",
            "mod sibling { macro_rules! decl_t { () => { pub struct T { pub y: u8 } }; } decl_t!(); } fn f() {}",
            "mod inner { macro_rules! decl_fn { () => { pub fn helper() -> u64 { 7u64 } }; } decl_fn!(); } fn f() {}",
            "macro_rules! p { ($t:ty) => { fn g(x: *const $t, y: fn(u8) -> u8) -> &'static str { \"\" } }; } p!(u8); fn f() {}",
            "macro_rules! m { () => { #[derive(Clone, PartialEq)] #[allow(dead_code)] struct Q; } } m!(); fn f() {}",
            "macro_rules! m { () => { $crate::n!() } } macro_rules! n { () => { 1 } } fn g() -> u64 { m!() } fn f() {}",
            // A macro that defines a macro and invokes it.
            "fn f() { let mut e = 0u64; macro_rules! outer { () => { macro_rules! inner { () => { e = 7u64; }; } inner!(); }; } outer!(); }",
            // A raw fragment the transcriber drops, with arguments that are
            // never expanded.
            "macro_rules! state_machine { ($($tokens:tt)*) => {}; } state_machine! { X { fields { pub t: u64 } } } fn f() {}",
            "macro_rules! state_machine { ($($tokens:tt)*) => { () }; } fn f() { state_machine! { X { transition! { tr() { update t = 5u64; } } impl Tr for u8 {} } }; }",
            // The file's macro reached through its own module, and re-exported.
            "mod m { macro_rules! assume { ($e:expr) => {}; } pub(crate) use assume; } fn g(x: u64) { m::assume!(x == 0u64); } fn f() {}",
            "use trust_vc::assume; mod m { macro_rules! assume { ($e:expr) => {}; } } fn f(x: u64) { assume!(x == 0u64); }",
            // A marker for trust_vc's own refused machine.
            "__trust_vc_state_machine_refused! { 0 3 \"state_machine! `W`: field `t` has type `Gen`\" } fn f() {}",
        ] {
            assert_eq!(hazard(src), None, "refused: {src}");
        }
    }

    #[test]
    fn the_refusal_names_the_hazard() {
        let src = "macro_rules! peq { ($t:ty) => { impl PartialEq for $t { fn eq(&self, _: &Self) -> bool { false } } } } struct P; peq!(P); fn f(p: P) { assert!(p == p); }";
        let file = syn::parse_file(src).expect("fixture parses");
        let func = match &file.items[3] {
            syn::Item::Fn(func) => func.clone(),
            _ => panic!("fixture has `fn f`"),
        };
        let message = verified_refusal(Some(&file), &func).expect("refused");
        assert!(message.starts_with(UNREAD_ITEM_TAG), "{message}");
        assert!(message.contains("peq!"), "{message}");
        assert!(message.contains("can expand to `impl`"), "{message}");
    }

    #[test]
    fn without_a_file_the_function_alone_is_read() {
        let func: ItemFn = syn::parse_quote! {
            fn f() { mk!(); }
        };
        assert!(verified_refusal(None, &func).is_some());
        let func: ItemFn = syn::parse_quote! {
            fn f(x: u64) { trust_vc::assert!(x == x); }
        };
        assert_eq!(verified_refusal(None, &func), None);
    }
}
