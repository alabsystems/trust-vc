// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Refuses a `Verified` answer for a function that reaches a method call
//! which Rust may resolve to a different method than the one this lane reads.
//!
//! The lane reads `recv.m(..)` on a primitive or std receiver as the std
//! method `m`, and on a value of a file type through the file's impls, where
//! an inherent method wins over a trait method of the same name. Rust walks
//! the receiver's autoderef steps and tries, at each step, the receiver by
//! value, then `&recv`, then `&mut recv`. The first position where some
//! method named `m` applies decides the call, and an inherent method wins
//! over a trait method only at that same position. So a trait method in
//! scope replaces a method of the same name that Rust would find later:
//!
//! * `trait MyClone { fn clone(self) -> Self; }` with `impl MyClone for u64`
//!   makes `x.clone()` on `x: u64` call `MyClone::clone`, which takes `self`
//!   by value, instead of the std `Clone::clone(&self)`;
//! * `trait P { fn push(&self, x: u64); }` with `impl P for Vec<u64>` makes
//!   `v.push(1)` call `P::push` instead of `Vec::push(&mut self)`;
//! * a blanket `impl<X> Len for X { fn len(self) -> usize { .. } }` replaces
//!   `Vec::len(&self)` on every `Vec`;
//! * `impl Tr for S { fn w(self) .. }` replaces the inherent `S::w(&self)` on
//!   a receiver of type `S`, a trait `fn eq(self, ..)` replaces the derived
//!   `PartialEq::eq(&self, ..)`, and `impl Iterator for C` makes `c.count()`
//!   call `Iterator::count(self)` instead of an inherent `C::count(&self)`.
//!
//! The lane does not order the candidates this way. So a function is refused
//! when it, or the body or contract of a function of the file it names
//! (transitively), contains a method call `.m(..)` whose name is at risk:
//!
//! * a method of a trait the file declares, when a type the lane reads with
//!   library methods may implement the trait and the method's name is one a
//!   library type has ([`library_method_name`]). Such an impl is one in the
//!   file for a type that is not a struct, enum or union of the file (a
//!   primitive, a std type, a tuple, an array, a type alias, a generic
//!   parameter), or one outside the file: the trait can be named outside the
//!   file's module (it and every inline module around it are not all
//!   private, or a `pub use` can re-export it), or the file declares an
//!   out-of-line `mod` or has an item-position macro, which may expand to
//!   one;
//! * a method of a trait the file declares whose name is also a method of a
//!   std trait that a type can have without an impl written in this file (a
//!   derive, a blanket impl or a bound; see [`KNOWN_TRAIT_METHODS`]), when
//!   that std trait is in the prelude or the file imports or names it;
//! * a method name an inherent impl and a trait (declared or implemented in
//!   the file) both declare with different receivers, or two traits declare
//!   with different receivers;
//! * a method name the file declares, when the file names a trait in an
//!   impl, a bound, a supertrait, `impl Trait` or `dyn Trait` that it does not
//!   declare and that [`KNOWN_TRAIT_METHODS`] does not list (`Iterator` has
//!   dozens of provided methods): every such name for a trait named through a
//!   path this file does not show, and every such name a library type has
//!   for a trait named bare or through `std`, `core` or `alloc`;
//! * every method name, where a `use` whose source the file does not show
//!   (`use other::MyClone;`, `use heapless::*;`, `use crate::m::Tr;`) can
//!   bring any trait into scope: the whole file for a `use` in a module, and
//!   the functions holding the block for a `use` in a block.
//!
//! The methods of an impl of a trait that operators, comparisons, `for`, `?`,
//! dereferences or formatting invoke without naming them are reached from
//! every function. A path call (`MyClone::clone(x)`, `Clone::clone(&x)`,
//! `S::w(&s)`) names the trait or type whose method it calls and is not
//! refused. Names are read as text, so a name at risk refuses every method
//! call spelled with it, on any receiver.
//!
//! A trait or an impl a macro declares is refused by `unread_items`. Not
//! covered: a std trait imported from `std` that gives a std type a second
//! method of the same name (`use std::borrow::BorrowMut;` with
//! `rc.borrow_mut()` on an `Rc<RefCell<T>>`).

use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

use proc_macro2::{Delimiter, Spacing, TokenStream, TokenTree};
use quote::ToTokens;
use syn::visit::Visit;
use syn::{File, ItemFn};

use super::bodiless_call_repeat::IMPLICIT_CALL_TRAITS;
use super::type_name_rebinding::{opaque_imports, OpaqueImport};

/// The tag every refusal from this module starts with.
pub(super) const TRAIT_METHOD_RESOLUTION_TAG: &str = "trait method resolution";

/// Std traits, and the lane's own `View` and `InvariantPredicate`, whose
/// methods are all known here, with every method that takes a `self`
/// receiver, and whether the trait is in the prelude. A type can have these
/// methods without an impl the file shows: through a derive, a blanket impl
/// (`Into`, `TryInto`, `ToOwned`, `ToString`, `Borrow`, `Any`), or a bound.
const KNOWN_TRAIT_METHODS: &[(&str, bool, &[&str])] = &[
    ("Clone", true, &["clone", "clone_from"]),
    ("Copy", true, &[]),
    ("PartialEq", true, &["eq", "ne"]),
    ("Eq", true, &["assert_receiver_is_total_eq"]),
    ("PartialOrd", true, &["partial_cmp", "lt", "le", "gt", "ge"]),
    ("Ord", true, &["cmp", "max", "min", "clamp"]),
    ("Default", true, &[]),
    ("Drop", true, &["drop"]),
    ("From", true, &[]),
    ("Into", true, &["into"]),
    ("TryFrom", true, &[]),
    ("TryInto", true, &["try_into"]),
    ("AsRef", true, &["as_ref"]),
    ("AsMut", true, &["as_mut"]),
    ("ToOwned", true, &["to_owned", "clone_into"]),
    ("ToString", true, &["to_string"]),
    ("Send", true, &[]),
    ("Sync", true, &[]),
    ("Sized", true, &[]),
    ("Unpin", true, &[]),
    ("Fn", true, &["call"]),
    ("FnMut", true, &["call_mut"]),
    ("FnOnce", true, &["call_once"]),
    ("Hash", false, &["hash"]),
    ("Debug", false, &["fmt"]),
    ("Display", false, &["fmt"]),
    ("Deref", false, &["deref"]),
    ("DerefMut", false, &["deref_mut"]),
    ("Borrow", false, &["borrow"]),
    ("BorrowMut", false, &["borrow_mut"]),
    ("Any", false, &["type_id"]),
    ("Add", false, &["add"]),
    ("Sub", false, &["sub"]),
    ("Mul", false, &["mul"]),
    ("Div", false, &["div"]),
    ("Rem", false, &["rem"]),
    ("Neg", false, &["neg"]),
    ("Not", false, &["not"]),
    ("BitAnd", false, &["bitand"]),
    ("BitOr", false, &["bitor"]),
    ("BitXor", false, &["bitxor"]),
    ("Shl", false, &["shl"]),
    ("Shr", false, &["shr"]),
    ("AddAssign", false, &["add_assign"]),
    ("SubAssign", false, &["sub_assign"]),
    ("MulAssign", false, &["mul_assign"]),
    ("DivAssign", false, &["div_assign"]),
    ("RemAssign", false, &["rem_assign"]),
    ("BitAndAssign", false, &["bitand_assign"]),
    ("BitOrAssign", false, &["bitor_assign"]),
    ("BitXorAssign", false, &["bitxor_assign"]),
    ("ShlAssign", false, &["shl_assign"]),
    ("ShrAssign", false, &["shr_assign"]),
    ("Index", false, &["index"]),
    ("IndexMut", false, &["index_mut"]),
    ("View", false, &["view"]),
    ("InvariantPredicate", false, &[]),
];

/// Crate roots whose traits this lane knows: its own crates, which declare
/// only `View` and `InvariantPredicate`.
const KNOWN_ROOTS: &[&str] = &["trust_vc", "trust_vc_types"];

/// The crate roots of the std library.
const STD_ROOTS: &[&str] = &["std", "core", "alloc"];

/// Names the lane reads as methods of its own on a value that is not of a
/// file type, beyond those a library declares.
const LANE_METHOD_NAMES: &[&str] = &[
    "after_borrow",
    "call_ensures",
    "call_requires",
    "decreases_to",
    "equal",
    "ext_eq",
    "ext_ne",
    "has_resolved",
    "has_resolved_unsized",
    "is_smaller_than",
    "mut_ref_current",
    "mut_ref_future",
    "spec_height",
    "strict_eq",
];

/// Every method name a type of the std library, vstd or trust-vc-types
/// declares, one per line, sorted; generated by
/// `scripts/gen_library_method_names.py`.
const LIBRARY_METHOD_NAMES: &str = include_str!("library_method_names.txt");

/// Whether a type this lane reads with library methods (a primitive, a std
/// or vstd type, a ghost type) can have a method named `name` that is not the
/// file's own.
fn library_method_name(name: &str) -> bool {
    static NAMES: OnceLock<BTreeSet<&'static str>> = OnceLock::new();
    LANE_METHOD_NAMES.contains(&name)
        || NAMES
            .get_or_init(|| LIBRARY_METHOD_NAMES.lines().collect())
            .contains(name)
}

/// The receiver of a method.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Receiver {
    /// `self`, `mut self`, `self: Self`.
    Value,
    /// `&self`, `self: &Self`.
    Shared,
    /// `&mut self`, `self: &mut Self`.
    Mutable,
    /// Any other typed receiver (`self: Box<Self>`).
    Other,
}

impl Receiver {
    fn of(sig: &syn::Signature) -> Option<Self> {
        let receiver = sig.receiver()?;
        if receiver.colon_token.is_none() {
            return Some(match (&receiver.reference, &receiver.mutability) {
                (None, _) => Self::Value,
                (Some(_), None) => Self::Shared,
                (Some(_), Some(_)) => Self::Mutable,
            });
        }
        Some(match strip_type(&receiver.ty) {
            syn::Type::Path(path) if path.qself.is_none() && path.path.is_ident("Self") => {
                Self::Value
            }
            syn::Type::Reference(reference) if is_self_type(&reference.elem) => {
                if reference.mutability.is_some() {
                    Self::Mutable
                } else {
                    Self::Shared
                }
            }
            _ => Self::Other,
        })
    }

    fn spelling(self) -> &'static str {
        match self {
            Self::Value => "`self`",
            Self::Shared => "`&self`",
            Self::Mutable => "`&mut self`",
            Self::Other => "a typed `self`",
        }
    }
}

fn strip_type(ty: &syn::Type) -> &syn::Type {
    match ty {
        syn::Type::Paren(paren) => strip_type(&paren.elem),
        syn::Type::Group(group) => strip_type(&group.elem),
        ty => ty,
    }
}

fn is_self_type(ty: &syn::Type) -> bool {
    matches!(strip_type(ty), syn::Type::Path(path) if path.qself.is_none() && path.path.is_ident("Self"))
}

fn unraw(ident: &syn::Ident) -> String {
    syn::ext::IdentExt::unraw(ident).to_string()
}

fn last_segment(path: &syn::Path) -> Option<String> {
    path.segments.last().map(|segment| unraw(&segment.ident))
}

/// A trait the file declares.
struct TraitDecl {
    name: String,
    /// The trait and the inline modules around it are all private, so only
    /// the file's own module and its children can name it.
    module_private: bool,
    /// Every method with a `self` receiver.
    methods: Vec<(String, Receiver)>,
}

/// An impl the file writes.
struct ImplDecl {
    /// The last segment of the trait path, or `None` for an inherent impl.
    trait_name: Option<String>,
    self_ty: syn::Type,
    /// The impl's own generic type parameters.
    type_params: BTreeSet<String>,
    /// Every method with a `self` receiver.
    methods: Vec<(String, Receiver)>,
}

/// A function, method or trait method of the file.
struct Entry {
    name: String,
    /// Its attributes, signature and body, as text.
    source: String,
    /// Every identifier in its attributes, signature and body.
    idents: BTreeSet<String>,
    /// Every method name it calls with `.name(..)`.
    calls: BTreeSet<String>,
    /// A method of an impl of an [`IMPLICIT_CALL_TRAITS`] trait.
    implicit: bool,
}

impl Entry {
    fn new(name: String, tokens: TokenStream, implicit: bool) -> Self {
        let mut idents = BTreeSet::new();
        let mut calls = BTreeSet::new();
        let source = tokens.to_string();
        scan_tokens(tokens, &mut idents, &mut calls);
        Self {
            name,
            source,
            idents,
            calls,
            implicit,
        }
    }
}

/// Every identifier in `tokens`, and every name a method call `.name(..)` or
/// `.name::<..>(..)` spells, at any group depth (so in macro and attribute
/// tokens too).
fn scan_tokens(tokens: TokenStream, idents: &mut BTreeSet<String>, calls: &mut BTreeSet<String>) {
    let flat: Vec<TokenTree> = tokens.into_iter().collect();
    let is_dot = |index: usize, spacing: Spacing| {
        matches!(&flat[index], TokenTree::Punct(punct)
            if punct.as_char() == '.' && punct.spacing() == spacing)
    };
    for (index, tree) in flat.iter().enumerate() {
        match tree {
            TokenTree::Group(group) => scan_tokens(group.stream(), idents, calls),
            TokenTree::Ident(ident) => {
                let name = unraw(ident);
                // `a..f(x)` is a range, not a method call: its second `.`
                // follows a joint one.
                let after_dot = index > 0
                    && is_dot(index - 1, Spacing::Alone)
                    && !(index > 1 && is_dot(index - 2, Spacing::Joint));
                let before_call = match flat.get(index + 1) {
                    Some(TokenTree::Group(group)) => group.delimiter() == Delimiter::Parenthesis,
                    Some(TokenTree::Punct(punct)) => punct.as_char() == ':',
                    _ => false,
                };
                if after_dot && before_call {
                    calls.insert(name.clone());
                }
                idents.insert(name);
            }
            _ => {}
        }
    }
}

/// A trait path in a bound, a supertrait, `impl Trait`, `dyn Trait` or a
/// trait impl: its last segment, and whether its source is not shown (a
/// path of two or more segments that does not start at a std root).
struct MentionedTrait {
    name: String,
    opaque_path: bool,
}

/// What the file declares, read from its syntax.
#[derive(Default)]
struct FileScan {
    traits: Vec<TraitDecl>,
    impls: Vec<ImplDecl>,
    /// Every struct, enum and union name.
    nominal_types: BTreeSet<String>,
    mentioned_traits: Vec<MentionedTrait>,
    /// Every name a `use` imports, by the name it has at its source.
    imported_names: BTreeSet<String>,
    /// A glob `use` over a std path, which imports every trait there.
    std_glob: bool,
    /// A `use` that can re-export a name outside the file's module: one that
    /// is not private and imports that name or a glob.
    reexported_names: BTreeSet<String>,
    reexports_glob: bool,
    /// A construct that can add an impl this file does not show.
    outside_impl_source: Option<String>,
    entries: Vec<Entry>,
    /// Whether the impl being walked is of an [`IMPLICIT_CALL_TRAITS`] trait.
    implicit_impl: Vec<bool>,
    /// Whether each inline module around the item being walked is private.
    module_private: Vec<bool>,
}

impl<'ast> Visit<'ast> for FileScan {
    fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
        self.nominal_types.insert(unraw(&item.ident));
        syn::visit::visit_item_struct(self, item);
    }

    fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
        self.nominal_types.insert(unraw(&item.ident));
        syn::visit::visit_item_enum(self, item);
    }

    fn visit_item_union(&mut self, item: &'ast syn::ItemUnion) {
        self.nominal_types.insert(unraw(&item.ident));
        syn::visit::visit_item_union(self, item);
    }

    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        if item.content.is_none() && self.outside_impl_source.is_none() {
            self.outside_impl_source = Some(format!("the out-of-line `mod {};`", item.ident));
        }
        self.module_private
            .push(matches!(item.vis, syn::Visibility::Inherited));
        syn::visit::visit_item_mod(self, item);
        self.module_private.pop();
    }

    fn visit_item_macro(&mut self, item: &'ast syn::ItemMacro) {
        if self.outside_impl_source.is_none() {
            let name = last_segment(&item.mac.path).unwrap_or_default();
            self.outside_impl_source = Some(format!("the item-position macro `{name}!`"));
        }
        syn::visit::visit_item_macro(self, item);
    }

    fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
        let reexport = !matches!(item.vis, syn::Visibility::Inherited);
        let mut leaves = Vec::new();
        use_leaves(&item.tree, &mut Vec::new(), &mut leaves);
        for (root, leaf) in leaves {
            let from_std = root
                .as_deref()
                .is_some_and(|root| STD_ROOTS.contains(&root));
            match leaf {
                Some(name) => {
                    if reexport {
                        self.reexported_names.insert(name.clone());
                    }
                    self.imported_names.insert(name);
                }
                None => {
                    self.reexports_glob |= reexport;
                    self.std_glob |= from_std;
                }
            }
        }
        syn::visit::visit_item_use(self, item);
    }

    fn visit_item_trait(&mut self, item: &'ast syn::ItemTrait) {
        let methods =
            item.items
                .iter()
                .filter_map(|trait_item| match trait_item {
                    syn::TraitItem::Fn(method) => Receiver::of(&method.sig)
                        .map(|receiver| (unraw(&method.sig.ident), receiver)),
                    _ => None,
                })
                .collect();
        let module_private = matches!(item.vis, syn::Visibility::Inherited)
            || self.module_private.iter().any(|private| *private);
        self.traits.push(TraitDecl {
            name: unraw(&item.ident),
            module_private,
            methods,
        });
        syn::visit::visit_item_trait(self, item);
    }

    fn visit_trait_item_fn(&mut self, item: &'ast syn::TraitItemFn) {
        self.entries.push(Entry::new(
            unraw(&item.sig.ident),
            item.to_token_stream(),
            false,
        ));
        syn::visit::visit_trait_item_fn(self, item);
    }

    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        let trait_name = item.trait_.as_ref().and_then(|(_, path, _)| {
            self.mention(path);
            last_segment(path)
        });
        let methods =
            item.items
                .iter()
                .filter_map(|impl_item| match impl_item {
                    syn::ImplItem::Fn(method) => Receiver::of(&method.sig)
                        .map(|receiver| (unraw(&method.sig.ident), receiver)),
                    _ => None,
                })
                .collect();
        let type_params = item
            .generics
            .type_params()
            .map(|param| unraw(&param.ident))
            .collect();
        let implicit = trait_name
            .as_deref()
            .is_some_and(|name| IMPLICIT_CALL_TRAITS.contains(&name));
        self.impls.push(ImplDecl {
            trait_name,
            self_ty: (*item.self_ty).clone(),
            type_params,
            methods,
        });
        self.implicit_impl.push(implicit);
        syn::visit::visit_item_impl(self, item);
        self.implicit_impl.pop();
    }

    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        let implicit = self.implicit_impl.last().copied().unwrap_or(false);
        self.entries.push(Entry::new(
            unraw(&item.sig.ident),
            item.to_token_stream(),
            implicit,
        ));
        syn::visit::visit_impl_item_fn(self, item);
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        // A function inside an impl body is not a method of that impl.
        self.implicit_impl.push(false);
        self.entries.push(Entry::new(
            unraw(&item.sig.ident),
            item.to_token_stream(),
            false,
        ));
        syn::visit::visit_item_fn(self, item);
        self.implicit_impl.pop();
    }

    fn visit_trait_bound(&mut self, bound: &'ast syn::TraitBound) {
        self.mention(&bound.path);
        syn::visit::visit_trait_bound(self, bound);
    }
}

/// The root and the leaf name (`None` for a glob) of every path a `use`
/// tree imports, by the name each leaf has at its source.
fn use_leaves(
    tree: &syn::UseTree,
    prefix: &mut Vec<String>,
    out: &mut Vec<(Option<String>, Option<String>)>,
) {
    let root = |prefix: &[String]| prefix.first().cloned();
    match tree {
        syn::UseTree::Path(path) => {
            prefix.push(unraw(&path.ident));
            use_leaves(&path.tree, prefix, out);
            prefix.pop();
        }
        syn::UseTree::Group(group) => {
            for item in &group.items {
                use_leaves(item, prefix, out);
            }
        }
        syn::UseTree::Name(leaf) => out.push((root(prefix), Some(unraw(&leaf.ident)))),
        syn::UseTree::Rename(rename) => out.push((root(prefix), Some(unraw(&rename.ident)))),
        syn::UseTree::Glob(_) => out.push((root(prefix), None)),
    }
}

impl FileScan {
    fn new(file: Option<&File>, func: &ItemFn) -> Self {
        let mut scan = Self::default();
        match file {
            Some(file) => scan.visit_file(file),
            // With no file, `func` is all there is to read.
            None => scan.visit_item_fn(func),
        }
        scan
    }

    fn mention(&mut self, path: &syn::Path) {
        let Some(name) = last_segment(path) else {
            return;
        };
        let root = path.segments.first().map(|segment| unraw(&segment.ident));
        let opaque_path = path.segments.len() > 1
            && !root
                .as_deref()
                .is_some_and(|root| STD_ROOTS.contains(&root));
        self.mentioned_traits
            .push(MentionedTrait { name, opaque_path });
    }

    /// Whether `ty`, the self type of an impl with the generic type
    /// parameters `type_params`, is a struct, enum or union of the file or a
    /// reference to one.
    fn is_file_type(&self, ty: &syn::Type, type_params: &BTreeSet<String>) -> bool {
        match strip_type(ty) {
            syn::Type::Reference(reference) => self.is_file_type(&reference.elem, type_params),
            syn::Type::Path(path)
                if path.qself.is_none()
                    && path.path.leading_colon.is_none()
                    && path.path.segments.len() == 1 =>
            {
                let name = unraw(&path.path.segments[0].ident);
                self.nominal_types.contains(&name) && !type_params.contains(&name)
            }
            _ => false,
        }
    }

    /// Why the file trait `decl` may be implemented for a type the lane reads
    /// with library methods, or `None` when every impl of it is in the file
    /// and for a struct, enum or union of the file.
    fn implemented_beyond_file_types(&self, decl: &TraitDecl) -> Option<String> {
        if !decl.module_private {
            return Some(
                "which code outside this file's module can name, and so implement for another \
                 type"
                    .to_string(),
            );
        }
        if self.reexports_glob || self.reexported_names.contains(&decl.name) {
            return Some(
                "which a `pub use` can re-export, so code outside this file's module can \
                 implement it for another type"
                    .to_string(),
            );
        }
        if let Some(source) = &self.outside_impl_source {
            return Some(format!("and {source} can hold an impl of it"));
        }
        self.impls
            .iter()
            .find(|imp| {
                imp.trait_name.as_deref() == Some(decl.name.as_str())
                    && !self.is_file_type(&imp.self_ty, &imp.type_params)
            })
            .map(|imp| {
                format!(
                    "which `impl {} for {}` implements for a type that is not a struct, enum or \
                     union of this file",
                    decl.name,
                    imp.self_ty.to_token_stream()
                )
            })
    }

    /// Whether the std trait `known`, outside the prelude, can be in scope
    /// for a method call: the file imports it, globs a std path, or names it
    /// in a bound or an impl without declaring a trait of that name.
    fn non_prelude_trait_reachable(&self, known: &str, declared: &BTreeSet<&str>) -> bool {
        self.std_glob
            || self.imported_names.contains(known)
            || (!declared.contains(known)
                && self
                    .mentioned_traits
                    .iter()
                    .any(|mentioned| mentioned.name == known))
    }

    /// Every method name at risk, with why.
    fn names_at_risk(&self) -> BTreeMap<String, String> {
        let mut risk: BTreeMap<String, String> = BTreeMap::new();
        let mut add = |name: &str, why: String| {
            risk.entry(name.to_string()).or_insert(why);
        };
        let declared: BTreeSet<&str> = self.traits.iter().map(|decl| decl.name.as_str()).collect();

        for decl in &self.traits {
            if let Some(reason) = self.implemented_beyond_file_types(decl) {
                for (method, _) in &decl.methods {
                    if library_method_name(method) {
                        add(
                            method,
                            format!(
                                "`{method}` is a method of the trait `{}`, {reason}, and a \
                                 library type has a method of that name too",
                                decl.name
                            ),
                        );
                    }
                }
            }
            for (method, _) in &decl.methods {
                let known = KNOWN_TRAIT_METHODS
                    .iter()
                    .find(|(known, prelude, methods)| {
                        methods.contains(&method.as_str())
                            && (*prelude || self.non_prelude_trait_reachable(known, &declared))
                    });
                if let Some((known, _, _)) = known {
                    add(
                        method,
                        format!(
                            "`{method}` is a method of the trait `{}` and of the trait `{known}`, \
                             which a type can implement without an impl this file shows",
                            decl.name
                        ),
                    );
                }
            }
        }

        // Receivers of every declaration of a name: inherent ones, and those of
        // traits (declared or implemented in the file).
        let mut inherent: BTreeMap<&str, BTreeSet<Receiver>> = BTreeMap::new();
        let mut traits: BTreeMap<&str, BTreeSet<Receiver>> = BTreeMap::new();
        for imp in &self.impls {
            let map = if imp.trait_name.is_some() {
                &mut traits
            } else {
                &mut inherent
            };
            for (method, receiver) in &imp.methods {
                map.entry(method.as_str()).or_default().insert(*receiver);
            }
        }
        for decl in &self.traits {
            for (method, receiver) in &decl.methods {
                traits.entry(method.as_str()).or_default().insert(*receiver);
            }
        }
        for (method, trait_receivers) in &traits {
            let mut all = trait_receivers.clone();
            if let Some(inherent_receivers) = inherent.get(method) {
                all.extend(inherent_receivers.iter().copied());
            }
            if all.len() > 1 {
                let spelled: Vec<&str> = all.iter().map(|receiver| receiver.spelling()).collect();
                add(
                    method,
                    format!(
                        "`{method}` is declared in this file with different receivers ({}), at \
                         least one of them by a trait",
                        spelled.join(", ")
                    ),
                );
            }
        }

        let unknown: Vec<&MentionedTrait> = self
            .mentioned_traits
            .iter()
            .filter(|mentioned| {
                !declared.contains(mentioned.name.as_str())
                    && !KNOWN_TRAIT_METHODS
                        .iter()
                        .any(|(known, _, _)| *known == mentioned.name.as_str())
            })
            .collect();
        if !unknown.is_empty() {
            let opaque = unknown.iter().find(|mentioned| mentioned.opaque_path);
            let named = opaque.unwrap_or(&unknown[0]);
            // An impl of such a trait declares that trait's own methods.
            let unknown_names: BTreeSet<&str> = unknown
                .iter()
                .map(|mentioned| mentioned.name.as_str())
                .collect();
            let methods = self
                .traits
                .iter()
                .flat_map(|decl| decl.methods.iter())
                .chain(
                    self.impls
                        .iter()
                        .filter(|imp| {
                            !imp.trait_name
                                .as_deref()
                                .is_some_and(|name| unknown_names.contains(name))
                        })
                        .flat_map(|imp| imp.methods.iter()),
                );
            for (method, _) in methods {
                if opaque.is_some() || library_method_name(method) {
                    add(
                        method,
                        format!(
                            "this file names the trait `{}`, whose methods are not listed here, \
                             and `{method}` is a method this file declares",
                            named.name
                        ),
                    );
                }
            }
        }
        risk
    }
}

/// The entries `own` reaches: every function of the file whose name it
/// mentions, transitively, and every method of an impl of an
/// [`IMPLICIT_CALL_TRAITS`] trait.
fn reached_entries<'a>(entries: &'a [Entry], own: &Entry) -> Vec<&'a Entry> {
    let mut by_name: BTreeMap<&str, Vec<&Entry>> = BTreeMap::new();
    for entry in entries {
        by_name.entry(entry.name.as_str()).or_default().push(entry);
    }
    let mut reached: Vec<&Entry> = entries.iter().filter(|entry| entry.implicit).collect();
    let mut pending: Vec<&str> = own
        .idents
        .iter()
        .chain(reached.iter().flat_map(|entry| entry.idents.iter()))
        .map(String::as_str)
        .collect();
    let mut expanded = BTreeSet::new();
    while let Some(name) = pending.pop() {
        if !expanded.insert(name) {
            continue;
        }
        for entry in by_name.get(name).into_iter().flatten() {
            reached.push(entry);
            pending.extend(entry.idents.iter().map(String::as_str));
        }
    }
    reached
}

fn message(why: &str, method: &str) -> String {
    format!(
        "{TRAIT_METHOD_RESOLUTION_TAG}: {why}, and this function reaches the method call \
         `.{method}(..)`. Rust tries the receiver by value, then `&`, then `&mut` at each \
         autoderef step and takes the first method that applies, with an inherent method first \
         only at the same position, so the call may run another method than the one this lane \
         reads. A `Verified` answer is refused; a refutation would be kept"
    )
}

fn unseen_import_message(import: &OpaqueImport, method: &str) -> String {
    message(
        &format!(
            "`use {}` imports from a source this file does not show, which can bring a trait \
             with a method of any name into scope",
            import.rendered
        ),
        method,
    )
}

/// The refusal message for a `Verified` answer of `func`, or `None` when no
/// method call `func` reaches can resolve to another method than the one
/// this lane reads. See the module documentation.
pub(super) fn verified_refusal(file: Option<&File>, func: &ItemFn) -> Option<String> {
    let scan = FileScan::new(file, func);
    let own = Entry::new(String::new(), func.to_token_stream(), false);
    let reached = reached_entries(&scan.entries, &own);
    let mut code: Vec<&Entry> = vec![&own];
    code.extend(reached);
    refusal(&scan, file, func, &code)
}

/// The refusal message for a `Verified` answer of a context built for the
/// whole file (trait conformance), which reads every function of the file.
pub(super) fn file_refusal(file: &File, probe: &ItemFn) -> Option<String> {
    let scan = FileScan::new(Some(file), probe);
    let code: Vec<&Entry> = scan.entries.iter().collect();
    refusal(&scan, Some(file), probe, &code)
}

/// The refusal for code made of the entries `code`, the first of which is
/// the function being verified.
fn refusal(scan: &FileScan, file: Option<&File>, func: &ItemFn, code: &[&Entry]) -> Option<String> {
    let calls: BTreeSet<&String> = code.iter().flat_map(|entry| entry.calls.iter()).collect();
    let first_call = calls.iter().next()?;
    for import in opaque_imports(file, func) {
        let root = import.rendered.trim_start_matches("::").split("::").next();
        if root.is_some_and(|root| KNOWN_ROOTS.contains(&root)) {
            continue;
        }
        let Some(block) = &import.block else {
            return Some(unseen_import_message(&import, first_call));
        };
        // A `use` in a block reaches the code of that block. When no function
        // of the file shows the block, it reaches the whole file.
        let block_source = block.to_token_stream().to_string();
        let holders: Vec<&Entry> = scan
            .entries
            .iter()
            .chain(code.iter().copied())
            .filter(|entry| entry.source.contains(&block_source))
            .collect();
        if holders.is_empty() {
            return Some(unseen_import_message(&import, first_call));
        }
        let reached_holder = code
            .iter()
            .find(|entry| !entry.calls.is_empty() && entry.source.contains(&block_source));
        if let Some(entry) = reached_holder {
            let method = entry.calls.iter().next()?;
            return Some(unseen_import_message(&import, method));
        }
    }
    let risk = scan.names_at_risk();
    calls
        .iter()
        .find_map(|method| risk.get(*method).map(|why| message(why, method)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn refusal_of(source: &str, name: &str) -> Option<String> {
        let file: File = syn::parse_str(source).expect("parse");
        let func = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == name => Some(func.clone()),
                _ => None,
            })
            .expect("function");
        verified_refusal(Some(&file), &func)
    }

    #[test]
    fn library_method_names_are_sorted_and_cover_std() {
        let names: Vec<&str> = LIBRARY_METHOD_NAMES.lines().collect();
        assert!(names.windows(2).all(|pair| pair[0] < pair[1]));
        for name in [
            "clone",
            "push",
            "len",
            "unwrap",
            "insert",
            "count",
            "view",
            "spec_index",
        ] {
            assert!(library_method_name(name), "{name}");
        }
        for name in ["area", "double", "default_returns_true"] {
            assert!(!library_method_name(name), "{name}");
        }
    }

    #[test]
    fn refused() {
        let cases = [
            // A by-value trait method on a primitive hides `Clone::clone`.
            "trait MyClone { fn clone(self) -> Self; } \
             impl MyClone for u64 { fn clone(self) -> Self { 7 } } \
             fn f(x: u64) -> u64 { x.clone() }",
            // A blanket impl reaches every type.
            "trait Len { fn len(self) -> usize; } \
             impl<X> Len for X { fn len(self) -> usize { 7 } } \
             fn f(v: Vec<u64>) -> usize { v.len() }",
            // A `&self` method hides `Vec::push(&mut self)`.
            "trait P { fn push(&self, x: u64); } \
             impl P for Vec<u64> { fn push(&self, _x: u64) {} } \
             fn f() { let mut v: Vec<u64> = Vec::new(); v.push(1); }",
            // A trait code outside the file's module can name may be
            // implemented there for `u64`.
            "pub trait Tr { fn len(&self) -> usize; } fn f(x: Vec<u64>) -> usize { x.len() }",
            "pub mod m { pub trait Tr { fn len(&self) -> usize; } } \
             fn f(x: Vec<u64>) -> usize { x.len() }",
            "mod m { pub trait Tr { fn len(&self) -> usize; } } pub use m::Tr; \
             fn f(x: Vec<u64>) -> usize { x.len() }",
            // An out-of-line module may implement the trait for `u64`.
            "mod other; trait Tr { fn len(&self) -> usize; } fn f(x: Vec<u64>) -> usize { x.len() }",
            // An item-position macro may expand to an impl.
            "trait Tr { fn len(&self) -> usize; } make_impl!(Tr); \
             fn f(x: Vec<u64>) -> usize { x.len() }",
            // An impl for a type alias names whatever type the alias does.
            "type A = u64; trait Tr { fn count_ones(&self) -> u32; } \
             impl Tr for A { fn count_ones(&self) -> u32 { 1 } } \
             fn f(x: u64) -> u32 { x.count_ones() }",
            // A std trait method name, even on a trait implemented only for a
            // file type: the derived `PartialEq::eq(&self)` loses to it.
            "#[derive(PartialEq)] struct S; trait MyEq { fn eq(self, o: &S) -> bool; } \
             impl MyEq for S { fn eq(self, _o: &S) -> bool { false } } \
             fn f(s: S) -> bool { s.eq(&s) }",
            // `std::ops::Add` imported makes `add` a method of `S` too.
            "use std::ops::Add; struct S; trait MyAdd { fn add(&self) -> u64; } \
             impl MyAdd for S { fn add(&self) -> u64 { 1 } } fn f(s: S) -> u64 { s.add() }",
            // An inherent `&self` method and a trait `self` method.
            "struct T; impl T { fn w(&self) -> u64 { 4 } } trait B { fn w(self) -> u64; } \
             impl B for T { fn w(self) -> u64 { 9 } } fn f(t: T) -> u64 { t.w() }",
            // `Iterator` gives `C` a by-value `count` that beats the inherent one.
            "struct C; impl Iterator for C { type Item = u64; \
             fn next(&mut self) -> Option<u64> { None } } \
             impl C { fn count(&self) -> usize { 5 } } fn f(c: C) -> usize { c.count() }",
            // A bound on a trait from another crate brings methods not listed
            // here.
            "struct S; impl S { fn w(&self) -> u64 { 4 } } \
             fn f<T: other::Tr>(t: T, s: S) -> u64 { s.w() }",
            // An import from another crate can bring any trait into scope.
            "use other::MyClone; fn f(x: u64) -> u64 { x.clone() }",
            "use heapless::*; fn f(x: u64) -> u64 { x.clone() }",
            "use crate::m::Tr; fn f(x: u64) -> u64 { x.clone() }",
            "fn f(x: u64) -> u64 { use other::Tr as _; x.clone() }",
            "fn f(x: u64) -> bool { assert!({ use other::Tr; true }); x.clone() == x }",
            // A `use` in the block of a function this one calls.
            "fn g(x: u64) -> u64 { use other::Tr; x.clone() } fn f(x: u64) -> u64 { g(x) }",
            // Reached through a callee's body.
            "trait MyClone { fn clone(self) -> Self; } \
             impl MyClone for u64 { fn clone(self) -> Self { 7 } } \
             fn g(x: u64) -> u64 { x.clone() } fn f(x: u64) -> u64 { g(x) }",
            // Reached through an operator impl, which `+` calls unnamed.
            "trait MyClone { fn clone(self) -> Self; } \
             impl MyClone for u64 { fn clone(self) -> Self { 7 } } \
             struct S(u64); impl std::ops::Add for S { type Output = S; \
             fn add(self, o: S) -> S { S(self.0.clone() + o.0) } } \
             fn f(a: S, b: S) -> S { a + b }",
            // In a contract.
            "trait MyClone { fn clone(self) -> Self; } \
             impl MyClone for u64 { fn clone(self) -> Self { 7 } } \
             #[trust_vc::ensures(result == x.clone())] fn f(x: u64) -> u64 { x }",
            // In macro tokens, with a turbofish.
            "trait Tr { fn get<T>(self) -> u64; } impl Tr for u64 { fn get<T>(self) -> u64 { 7 } } \
             fn f(x: u64) { assert!(x.get::<u8>() == 7); }",
        ];
        for source in cases {
            let refusal = refusal_of(source, "f");
            assert!(
                refusal
                    .as_deref()
                    .is_some_and(|message| message.starts_with(TRAIT_METHOD_RESOLUTION_TAG)),
                "{source}: {refusal:?}"
            );
        }
    }

    #[test]
    fn not_refused() {
        let cases = [
            // No trait: the std method.
            "fn f(x: u64) -> u64 { x.clone() }",
            // A path call names its trait.
            "trait MyClone { fn clone(self) -> Self; } \
             impl MyClone for u64 { fn clone(self) -> Self { 7 } } \
             fn f(x: u64) -> u64 { Clone::clone(&x) }",
            // A private trait implemented only for a file type, with a name no
            // library type has and one receiver.
            "trait Shape { fn area(&self) -> u64; } struct Sq(u64); \
             impl Shape for Sq { fn area(&self) -> u64 { self.0 } } \
             fn f(s: Sq, x: u64) -> u64 { s.area() + x.clone() }",
            // A trait implemented for `bool`, or public, whose method name no
            // library type has.
            "trait Flag { fn flag(self) -> bool; } impl Flag for bool { fn flag(self) -> bool { self } } \
             fn f(b: bool) -> bool { b.flag() }",
            "pub trait Shape { fn area(&self) -> u64; } pub struct Sq(pub u64); \
             impl Shape for Sq { fn area(&self) -> u64 { self.0 } } fn f(s: Sq) -> u64 { s.area() }",
            // A `pub` trait inside a private module, not re-exported.
            "mod m { pub trait Tr { fn len(&self) -> usize; } pub struct S; \
             impl Tr for S { fn len(&self) -> usize { 1 } } } \
             fn f(x: Vec<u64>) -> usize { x.len() }",
            // An impl for a reference to a file type.
            "trait Shape { fn area(self) -> u64; } struct Sq(u64); \
             impl Shape for &Sq { fn area(self) -> u64 { self.0 } } \
             fn f(s: &Sq) -> u64 { s.area() }",
            // Inherent and trait methods of one name and one receiver: the
            // inherent one wins at every position.
            "struct T; impl T { fn w(&self) -> u64 { 4 } } trait B { fn w(&self) -> u64; } \
             impl B for T { fn w(&self) -> u64 { 9 } } fn f(t: &T) -> u64 { t.w() }",
            // A file trait named `Add` with no `std::ops::Add` in scope.
            "trait Add { fn add(&self) -> u64; } struct S; \
             impl Add for S { fn add(&self) -> u64 { 1 } } fn f(s: S) -> u64 { s.add() }",
            // Imports from std and from the lane's own crates.
            "use std::collections::HashMap; use trust_vc_types::View; use std::ops::*; \
             fn f(x: u64) -> u64 { x.clone() }",
            // An import from an inline module of the file.
            "mod m { pub fn g() {} } use m::g; fn f(x: u64) -> u64 { g(); x.clone() }",
            // A function that reaches no method call.
            "use other::MyClone; fn f(x: u64) -> u64 { x + 1 }",
            // A `use` in the block of a function this one does not reach.
            "fn g(x: u64) -> u64 { use other::Tr; x.clone() } fn f(x: u64) -> u64 { x.clone() }",
            // A risky name in a function this one does not reach.
            "trait MyClone { fn clone(self) -> Self; } \
             impl MyClone for u64 { fn clone(self) -> Self { 7 } } \
             fn g(x: u64) -> u64 { x.clone() } fn f(x: u64) -> u64 { x.min(3) }",
            // Known bounds, and a std trait outside the list whose methods no
            // declaration of the file shares.
            "trait Tr { fn m(&self) -> u64; } struct S; impl Tr for S { fn m(&self) -> u64 { 1 } } \
             fn f<T: Clone + PartialEq + trust_vc_types::View, G: Fn(u64) -> u64, \
             I: Iterator<Item = u64>>(t: T, g: G, i: I, s: S) -> u64 { s.m() }",
            // A file trait of its own named `View`.
            "trait View { fn view(&self) -> u64; } struct S; \
             impl View for S { fn view(&self) -> u64 { 1 } } fn f(s: S) -> u64 { s.view() }",
            // An impl of `Iterator` declares `Iterator`'s own `next`.
            "struct C; impl Iterator for C { type Item = u64; \
             fn next(&mut self) -> Option<u64> { None } } \
             fn f(mut c: C) -> Option<u64> { c.next() }",
            // A field read and a range are not method calls.
            "trait Tr { fn m(self) -> u64; } impl Tr for u64 { fn m(self) -> u64 { 7 } } \
             struct S { m: u64 } fn f(s: S) -> u64 { for _ in 0..s.m {} s.m }",
            "trait Tr { fn g(self) -> u64; } impl Tr for u64 { fn g(self) -> u64 { 7 } } \
             fn g(x: u64) -> u64 { x } fn f(x: u64) { for _ in 0..g(x) {} }",
        ];
        for source in cases {
            let refusal = refusal_of(source, "f");
            assert!(refusal.is_none(), "{source}: {refusal:?}");
        }
    }
}
