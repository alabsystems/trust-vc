// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Refuses a `Verified` answer for a function that can drop a value whose
//! type runs a `Drop` impl of the file.
//!
//! Rust calls `Drop::drop` wherever a value is dropped: at the end of the
//! scope that owns it, when a place holding it is overwritten, at
//! `drop(x)`, and at the end of the statement for a temporary. The drop glue
//! of a struct, an enum, a tuple, an array or a collection runs the
//! destructors of the values it holds. The lane models none of these calls,
//! so a panic, an overflow or a callee precondition in a `drop` body is never
//! an obligation of the function that drops the value, and a write the
//! destructor makes through a reference it holds is not seen either. With
//! `impl Drop for D { fn drop(&mut self) { panic!("drop") } }`, `fn dr(d: D)
//! {}` was `Verified`, and so was `assert!(v.len() == 1)` after the scope of
//! a guard whose destructor clears the borrowed `Vec` `v`.
//!
//! Which names can stand for a value with such a destructor is read from the
//! text of the file:
//!
//! * the self type of each `impl Drop for ..`, and the type that an alias or
//!   a `use .. as ..` of that name stands for;
//! * each struct, enum and union of the file when the file declares an
//!   out-of-line `mod`, because that module can implement `Drop` for them;
//! * then, to a fixed point, each struct, enum, union, type alias, `const`
//!   and `static` whose tokens name one of these, each trait whose
//!   signatures or associated items name one, each variant of such an enum,
//!   each `use .. as ..` rename of such a name, each associated `const` of
//!   an impl that names one, and the self type of an impl whose associated
//!   types name one (for an impl whose self type is not a type of the file,
//!   its trait instead), since a `for` loop or a projection reaches those
//!   types without naming them;
//! * then, to a fixed point, each function, method, trait method and
//!   foreign function whose attributes, signature or body, or the header and
//!   associated items of the impl or trait around it, name one of these, and
//!   each rename of such a function. A method of an impl whose self type
//!   names one of these is left out: calling it needs a receiver or a path
//!   that already names that type.
//!
//! A function is refused when its attributes, signature or body, or the
//! header and associated items of the impl or trait around it, name any of
//! these. Every function of the file is refused when a method of an impl of
//! a trait that syntax calls without naming the method (an operator, a
//! comparison, `for`, `?`, a dereference, formatting) names one, unless the
//! impl's self type does. A method the file does not show is refused, since
//! the type of its impl is unknown. Names are read as text, so a same-named
//! local, generic parameter or method counts too. Over-reading a name only
//! refuses more.
//!
//! Not covered: a value of a generic type or of a `dyn` trait. The lane
//! assumes a generic value's destructor panics nowhere and writes nothing it
//! reads. A function of the file that puts a value of a file type with a
//! destructor into a generic or `dyn` value names that type, and is refused.
//! A `Drop` impl only another file shows is not seen here, except where the
//! crate lane appends its sibling files' `Drop` impls to the file it reads.

use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use syn::visit::Visit;
use syn::{File, ItemFn};

use super::bodiless_call_repeat::IMPLICIT_CALL_TRAITS;

/// The tag every refusal from this module starts with.
pub(super) const DROP_GLUE_TAG: &str = "unmodeled drop";

/// The refusal message for a `Verified` answer of `func`, or `None` when
/// `func` names nothing that can hold a value whose type has a `Drop` impl
/// of the file. Without a file, `func` alone is read.
pub(super) fn verified_refusal(file: Option<&File>, func: &ItemFn) -> Option<String> {
    let lone;
    let file = match file {
        Some(file) => file,
        None => {
            lone = File {
                shebang: None,
                attrs: Vec::new(),
                items: vec![syn::Item::Fn(func.clone())],
            };
            &lone
        }
    };
    if !may_have_seeds(file) {
        return None;
    }
    let scan = Scan::new(file);
    if scan.seeds.is_empty() {
        return None;
    }
    let carriers = scan.carriers();
    let func_name = unraw(&func.sig.ident);
    let mut named = fn_idents(&func.attrs, &func.sig, Some(&func.block));
    let source = fn_source(&func.sig, Some(&func.block));
    let same_name: Vec<&FnEntry> = scan
        .fns
        .iter()
        .filter(|entry| entry.name == func_name)
        .collect();
    let exact: Vec<&FnEntry> = same_name
        .iter()
        .copied()
        .filter(|entry| entry.source == source)
        .collect();
    for entry in if exact.is_empty() { &same_name } else { &exact } {
        named.extend(entry.context.iter().cloned());
    }
    if let Some(hit) = carriers.first_in(&named) {
        return Some(message("this function", hit, &carriers));
    }
    // A method the file does not show has an impl the rule cannot read.
    if same_name.is_empty() && (func.sig.receiver().is_some() || named.contains("Self")) {
        return Some(format!(
            "{DROP_GLUE_TAG}: the file does not show the impl of this method, whose self type \
             can run a destructor this lane does not model. A `Verified` answer is refused; a \
             refutation would be kept"
        ));
    }
    // An operator, a comparison, a `for` loop, `?`, a dereference or a format
    // call runs a method of such an impl without naming it.
    scan.fns.iter().find_map(|entry| {
        let trait_name = entry.trait_impl.as_deref()?;
        if trait_name == "Drop" || !IMPLICIT_CALL_TRAITS.contains(&trait_name) {
            return None;
        }
        if carriers.first_in(&entry.self_type).is_some() {
            return None;
        }
        let hit = carriers.first_in(entry.own.iter().chain(&entry.context))?;
        Some(message(
            &format!(
                "the `{trait_name}` impl method `{}`, which syntax can call without naming it,",
                entry.name
            ),
            hit,
            &carriers,
        ))
    })
}

/// The refusal message for a `Verified` answer of a context built for the
/// whole file (trait conformance), which reads the methods of the trait
/// impls of the file and the functions they name.
pub(super) fn file_refusal(file: &File) -> Option<String> {
    if !may_have_seeds(file) {
        return None;
    }
    let scan = Scan::new(file);
    if scan.seeds.is_empty() {
        return None;
    }
    let carriers = scan.carriers();
    scan.fns
        .iter()
        .filter(|entry| {
            entry
                .trait_impl
                .as_deref()
                .is_some_and(|name| name != "Drop")
        })
        .find_map(|entry| {
            let hit = carriers.first_in(entry.own.iter().chain(&entry.context))?;
            Some(message(
                &format!("the trait impl method `{}`", entry.name),
                hit,
                &carriers,
            ))
        })
}

/// False only when the file has no `impl .. Drop for ..` and no out-of-line
/// `mod`, anywhere: then no type of the file has a destructor it shows.
fn may_have_seeds(file: &File) -> bool {
    struct Finder(bool);
    impl<'ast> Visit<'ast> for Finder {
        fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
            let is_drop = item
                .trait_
                .as_ref()
                .and_then(|(_, path, _)| path.segments.last())
                .is_some_and(|segment| unraw(&segment.ident) == "Drop");
            self.0 |= is_drop;
            syn::visit::visit_item_impl(self, item);
        }
        fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
            self.0 |= item.content.is_none();
            syn::visit::visit_item_mod(self, item);
        }
    }
    let mut finder = Finder(false);
    finder.visit_file(file);
    finder.0
}

fn message(subject: &str, hit: &str, carriers: &Carriers) -> String {
    let mut chain = vec![hit.to_string()];
    let mut current = hit.to_string();
    while let Some(Cause::Names(next)) = carriers.cause.get(&current) {
        if chain.contains(next) {
            break;
        }
        chain.push(next.clone());
        current = next.clone();
    }
    let reason = match carriers.cause.get(&current) {
        Some(Cause::Seed(reason)) => reason.clone(),
        _ => "it has a `Drop` impl".to_string(),
    };
    let path = chain
        .iter()
        .map(|name| format!("`{name}`"))
        .collect::<Vec<_>>()
        .join(", which names ");
    format!(
        "{DROP_GLUE_TAG}: {subject} names {path}, and `{current}` can run a destructor ({reason}). \
         The lane does not run a destructor where a value is dropped, so a panic in it or a \
         write it makes is not seen. A `Verified` answer is refused; a refutation would be kept"
    )
}

/// Why a name can stand for a value with a destructor.
enum Cause {
    /// A type with a `Drop` impl, and how the file shows it.
    Seed(String),
    /// A name whose tokens name this other carrier.
    Names(String),
}

/// Every name that can stand for a value with a destructor.
struct Carriers {
    cause: BTreeMap<String, Cause>,
}

impl Carriers {
    fn contains(&self, name: &str) -> bool {
        self.cause.contains_key(name)
    }

    fn first_in<'a>(&self, names: impl IntoIterator<Item = &'a String>) -> Option<&'a String> {
        names.into_iter().find(|name| self.contains(name))
    }

    /// Adds each `(name, cause)` whose name is new; true when one was.
    fn insert_all(&mut self, added: Vec<(String, String)>) -> bool {
        let mut changed = false;
        for (name, cause) in added {
            if !self.contains(&name) {
                self.cause.insert(name, Cause::Names(cause));
                changed = true;
            }
        }
        changed
    }
}

/// A struct, enum, union, type alias, trait, `const` or `static`.
struct TypeNode {
    name: String,
    idents: BTreeSet<String>,
}

/// The associated types of an impl.
struct ImplAssoc {
    /// The last segment of the self type, when it is a path.
    self_type: Option<String>,
    /// The last segment of the implemented trait.
    trait_name: Option<String>,
    idents: BTreeSet<String>,
}

/// A function, a method or a trait method.
struct FnEntry {
    name: String,
    /// The signature and body as text, which tells same-named entries apart.
    source: String,
    /// The identifiers of its attributes, signature (without its own name)
    /// and body.
    own: BTreeSet<String>,
    /// The identifiers of the header and associated items of the impl or
    /// trait around it.
    context: BTreeSet<String>,
    /// The identifiers of the self type of the impl around it, its generic
    /// parameters left out.
    self_type: BTreeSet<String>,
    /// The last segment of the trait the impl around it implements.
    trait_impl: Option<String>,
}

/// The impl or trait around the items being visited.
#[derive(Clone, Default)]
struct Frame {
    context: BTreeSet<String>,
    self_type: BTreeSet<String>,
    trait_impl: Option<String>,
}

#[derive(Default)]
struct Scan {
    /// Each type with a `Drop` impl, and how the file shows it.
    seeds: BTreeMap<String, String>,
    types: Vec<TypeNode>,
    /// The variants of each enum.
    variants: BTreeMap<String, Vec<String>>,
    /// `use .. X as Y` renames, as `(Y, X)`.
    renames: Vec<(String, String)>,
    /// Type aliases whose right side is a path, as `(alias, last segment)`.
    alias_targets: Vec<(String, String)>,
    impl_assocs: Vec<ImplAssoc>,
    fns: Vec<FnEntry>,
    /// The structs, enums and unions of the file.
    nominal: BTreeSet<String>,
    /// The type aliases of the file.
    aliases: BTreeSet<String>,
    /// The first out-of-line `mod` of the file.
    out_of_line_mod: Option<String>,
    frames: Vec<Frame>,
}

impl Scan {
    fn new(file: &File) -> Self {
        let mut scan = Scan::default();
        scan.visit_file(file);
        if let Some(module) = scan.out_of_line_mod.clone() {
            for name in scan.nominal.clone() {
                scan.seeds.entry(name).or_insert_with(|| {
                    format!("the out-of-line `mod {module};` can implement `Drop` for it")
                });
            }
        }
        // An alias or a rename with a `Drop` impl is the type it stands for.
        loop {
            let mut added = Vec::new();
            let targets = scan.alias_targets.iter().chain(&scan.renames);
            for (alias, target) in targets {
                if let Some(reason) = scan.seeds.get(alias) {
                    if !scan.seeds.contains_key(target) {
                        added.push((target.clone(), reason.clone()));
                    }
                }
            }
            if added.is_empty() {
                break;
            }
            for (name, reason) in added {
                scan.seeds.entry(name).or_insert(reason);
            }
        }
        scan
    }

    fn carriers(&self) -> Carriers {
        let mut carriers = Carriers {
            cause: self
                .seeds
                .iter()
                .map(|(name, reason)| (name.clone(), Cause::Seed(reason.clone())))
                .collect(),
        };
        loop {
            let mut added: Vec<(String, String)> = Vec::new();
            for node in &self.types {
                if !carriers.contains(&node.name) {
                    if let Some(hit) = carriers.first_in(&node.idents) {
                        added.push((node.name.clone(), hit.clone()));
                    }
                }
            }
            for (owner, variants) in &self.variants {
                if carriers.contains(owner) {
                    for variant in variants {
                        added.push((variant.clone(), owner.clone()));
                    }
                }
            }
            for (renamed, source) in &self.renames {
                if carriers.contains(source) {
                    added.push((renamed.clone(), source.clone()));
                }
            }
            for assoc in &self.impl_assocs {
                let Some(hit) = carriers.first_in(&assoc.idents) else {
                    continue;
                };
                let carrier = match (&assoc.self_type, &assoc.trait_name) {
                    (Some(name), _) if self.declares_type(name) => Some(name),
                    (_, Some(trait_name)) => Some(trait_name),
                    (self_type, None) => self_type.as_ref(),
                };
                if let Some(carrier) = carrier {
                    added.push((carrier.clone(), hit.clone()));
                }
            }
            if !carriers.insert_all(added) {
                break;
            }
        }
        // The self types are settled now. A method of an impl for one of them
        // is reached only through a name that already stands for that type.
        let in_carrier_impl: Vec<bool> = self
            .fns
            .iter()
            .map(|entry| carriers.first_in(&entry.self_type).is_some())
            .collect();
        loop {
            let mut added: Vec<(String, String)> = Vec::new();
            for (entry, skip) in self.fns.iter().zip(&in_carrier_impl) {
                if *skip || carriers.contains(&entry.name) {
                    continue;
                }
                if let Some(hit) = carriers.first_in(entry.own.iter().chain(&entry.context)) {
                    added.push((entry.name.clone(), hit.clone()));
                }
            }
            for (renamed, source) in &self.renames {
                if carriers.contains(source) {
                    added.push((renamed.clone(), source.clone()));
                }
            }
            if !carriers.insert_all(added) {
                break;
            }
        }
        carriers
    }

    /// True when the file declares a struct, enum, union or type alias of
    /// this name.
    fn declares_type(&self, name: &str) -> bool {
        self.nominal.contains(name) || self.aliases.contains(name)
    }

    fn frame(&self) -> Frame {
        self.frames.last().cloned().unwrap_or_default()
    }

    fn record_fn(
        &mut self,
        attrs: &[syn::Attribute],
        sig: &syn::Signature,
        block: Option<&syn::Block>,
    ) {
        let frame = self.frame();
        self.fns.push(FnEntry {
            name: unraw(&sig.ident),
            source: fn_source(sig, block),
            own: fn_idents(attrs, sig, block),
            context: frame.context,
            self_type: frame.self_type,
            trait_impl: frame.trait_impl,
        });
    }

    fn type_node(&mut self, ident: &syn::Ident, tokens: TokenStream) {
        self.types.push(TypeNode {
            name: unraw(ident),
            idents: idents(tokens),
        });
    }

    /// Visits the inside of a function. An item declared in a body cannot
    /// name the `Self` of the impl or trait around the function.
    fn in_body(&mut self, visit: impl FnOnce(&mut Self)) {
        self.frames.push(Frame::default());
        visit(self);
        self.frames.pop();
    }
}

impl<'ast> Visit<'ast> for Scan {
    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        let generic_params = generic_param_names(&item.generics);
        let trait_name = item
            .trait_
            .as_ref()
            .and_then(|(_, path, _)| path.segments.last())
            .map(|segment| unraw(&segment.ident));
        let self_last = type_path_last(&item.self_ty);
        if trait_name.as_deref() == Some("Drop") {
            let names: Vec<String> = match &self_last {
                Some(name) => vec![name.clone()],
                None => idents(item.self_ty.to_token_stream())
                    .into_iter()
                    .filter(|name| !generic_params.contains(name))
                    .collect(),
            };
            for name in names {
                let reason = format!("`impl Drop for {name}`");
                self.seeds.entry(name).or_insert(reason);
            }
        }
        let mut assoc_types = TokenStream::new();
        let mut assoc_consts = TokenStream::new();
        for impl_item in &item.items {
            match impl_item {
                syn::ImplItem::Type(ty) => ty.to_tokens(&mut assoc_types),
                syn::ImplItem::Const(constant) => {
                    constant.to_tokens(&mut assoc_consts);
                    let mut tokens = constant.ty.to_token_stream();
                    constant.expr.to_tokens(&mut tokens);
                    self.type_node(&constant.ident, tokens);
                }
                _ => {}
            }
        }
        self.impl_assocs.push(ImplAssoc {
            self_type: self_last,
            trait_name: trait_name.clone(),
            idents: idents(assoc_types.clone()),
        });
        let mut header = item.generics.to_token_stream();
        item.generics.where_clause.to_tokens(&mut header);
        if let Some((_, path, _)) = &item.trait_ {
            path.to_tokens(&mut header);
        }
        item.self_ty.to_tokens(&mut header);
        header.extend(assoc_types);
        header.extend(assoc_consts);
        let self_type = idents(item.self_ty.to_token_stream())
            .into_iter()
            .filter(|name| !generic_params.contains(name))
            .collect();
        self.frames.push(Frame {
            context: idents(header),
            self_type,
            trait_impl: trait_name,
        });
        syn::visit::visit_item_impl(self, item);
        self.frames.pop();
    }

    fn visit_item_trait(&mut self, item: &'ast syn::ItemTrait) {
        // The generics, supertraits and associated items, with each method's
        // signature but not its default body.
        let mut header = item.generics.to_token_stream();
        item.generics.where_clause.to_tokens(&mut header);
        item.supertraits.to_tokens(&mut header);
        for trait_item in &item.items {
            match trait_item {
                syn::TraitItem::Fn(method) => method.sig.to_tokens(&mut header),
                other => other.to_tokens(&mut header),
            }
        }
        self.type_node(&item.ident, header.clone());
        self.frames.push(Frame {
            context: idents(header),
            self_type: BTreeSet::new(),
            trait_impl: None,
        });
        syn::visit::visit_item_trait(self, item);
        self.frames.pop();
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        // A function declared in a body has no impl or trait around it.
        self.in_body(|scan| {
            scan.record_fn(&item.attrs, &item.sig, Some(&item.block));
            syn::visit::visit_item_fn(scan, item);
        });
    }

    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        self.record_fn(&item.attrs, &item.sig, Some(&item.block));
        self.in_body(|scan| syn::visit::visit_impl_item_fn(scan, item));
    }

    fn visit_trait_item_fn(&mut self, item: &'ast syn::TraitItemFn) {
        self.record_fn(&item.attrs, &item.sig, item.default.as_ref());
        self.in_body(|scan| syn::visit::visit_trait_item_fn(scan, item));
    }

    fn visit_foreign_item_fn(&mut self, item: &'ast syn::ForeignItemFn) {
        self.in_body(|scan| scan.record_fn(&item.attrs, &item.sig, None));
        syn::visit::visit_foreign_item_fn(self, item);
    }

    fn visit_foreign_item_static(&mut self, item: &'ast syn::ForeignItemStatic) {
        self.type_node(&item.ident, item.ty.to_token_stream());
        syn::visit::visit_foreign_item_static(self, item);
    }

    fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
        self.nominal.insert(unraw(&item.ident));
        self.type_node(&item.ident, item.to_token_stream());
        syn::visit::visit_item_struct(self, item);
    }

    fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
        let name = unraw(&item.ident);
        self.nominal.insert(name.clone());
        self.type_node(&item.ident, item.to_token_stream());
        self.variants
            .entry(name)
            .or_default()
            .extend(item.variants.iter().map(|variant| unraw(&variant.ident)));
        syn::visit::visit_item_enum(self, item);
    }

    fn visit_item_union(&mut self, item: &'ast syn::ItemUnion) {
        self.nominal.insert(unraw(&item.ident));
        self.type_node(&item.ident, item.to_token_stream());
        syn::visit::visit_item_union(self, item);
    }

    fn visit_item_type(&mut self, item: &'ast syn::ItemType) {
        let name = unraw(&item.ident);
        self.aliases.insert(name.clone());
        if let Some(target) = type_path_last(&item.ty) {
            self.alias_targets.push((name, target));
        }
        let mut tokens = item.generics.to_token_stream();
        item.ty.to_tokens(&mut tokens);
        self.type_node(&item.ident, tokens);
        syn::visit::visit_item_type(self, item);
    }

    fn visit_item_const(&mut self, item: &'ast syn::ItemConst) {
        let mut tokens = item.ty.to_token_stream();
        item.expr.to_tokens(&mut tokens);
        self.type_node(&item.ident, tokens);
        self.in_body(|scan| syn::visit::visit_item_const(scan, item));
    }

    fn visit_item_static(&mut self, item: &'ast syn::ItemStatic) {
        let mut tokens = item.ty.to_token_stream();
        item.expr.to_tokens(&mut tokens);
        self.type_node(&item.ident, tokens);
        self.in_body(|scan| syn::visit::visit_item_static(scan, item));
    }

    fn visit_use_rename(&mut self, rename: &'ast syn::UseRename) {
        self.renames
            .push((unraw(&rename.rename), unraw(&rename.ident)));
        syn::visit::visit_use_rename(self, rename);
    }

    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        if item.content.is_none() && self.out_of_line_mod.is_none() {
            self.out_of_line_mod = Some(unraw(&item.ident));
        }
        syn::visit::visit_item_mod(self, item);
    }
}

/// The identifiers of a function's attributes, signature without its own
/// name, and body.
fn fn_idents(
    attrs: &[syn::Attribute],
    sig: &syn::Signature,
    block: Option<&syn::Block>,
) -> BTreeSet<String> {
    let mut tokens = TokenStream::new();
    for attr in attrs {
        attr.to_tokens(&mut tokens);
    }
    sig.generics.to_tokens(&mut tokens);
    sig.generics.where_clause.to_tokens(&mut tokens);
    sig.inputs.to_tokens(&mut tokens);
    sig.output.to_tokens(&mut tokens);
    if let Some(block) = block {
        block.to_tokens(&mut tokens);
    }
    idents(tokens)
}

fn fn_source(sig: &syn::Signature, block: Option<&syn::Block>) -> String {
    let mut source = sig.to_token_stream().to_string();
    if let Some(block) = block {
        source.push_str(&block.to_token_stream().to_string());
    }
    source
}

/// Every identifier in `tokens`, at any depth, lifetimes left out.
fn idents(tokens: TokenStream) -> BTreeSet<String> {
    fn walk(tokens: TokenStream, out: &mut BTreeSet<String>) {
        let mut after_quote = false;
        for tree in tokens {
            match &tree {
                TokenTree::Ident(ident) => {
                    if !after_quote {
                        out.insert(unraw(ident));
                    }
                }
                TokenTree::Group(group) => walk(group.stream(), out),
                TokenTree::Punct(_) | TokenTree::Literal(_) => {}
            }
            after_quote = matches!(&tree, TokenTree::Punct(p) if p.as_char() == '\'');
        }
    }
    let mut out = BTreeSet::new();
    walk(tokens, &mut out);
    out
}

/// The last segment of a path type, through parentheses and groups.
fn type_path_last(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Path(path) => path
            .path
            .segments
            .last()
            .map(|segment| unraw(&segment.ident)),
        syn::Type::Paren(paren) => type_path_last(&paren.elem),
        syn::Type::Group(group) => type_path_last(&group.elem),
        _ => None,
    }
}

fn generic_param_names(generics: &syn::Generics) -> BTreeSet<String> {
    generics
        .params
        .iter()
        .filter_map(|param| match param {
            syn::GenericParam::Type(ty) => Some(unraw(&ty.ident)),
            syn::GenericParam::Const(constant) => Some(unraw(&constant.ident)),
            syn::GenericParam::Lifetime(_) => None,
        })
        .collect()
}

fn unraw(ident: &proc_macro2::Ident) -> String {
    syn::ext::IdentExt::unraw(ident).to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The function or method `name` of `src`, as the extraction receives it.
    fn target(file: &File, name: &str) -> ItemFn {
        struct Finder<'n> {
            name: &'n str,
            found: Option<ItemFn>,
        }
        impl<'ast> Visit<'ast> for Finder<'_> {
            fn visit_item_fn(&mut self, item: &'ast ItemFn) {
                if item.sig.ident == self.name && self.found.is_none() {
                    self.found = Some(item.clone());
                }
                syn::visit::visit_item_fn(self, item);
            }
            fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
                if item.sig.ident == self.name && self.found.is_none() {
                    self.found = Some(ItemFn {
                        attrs: item.attrs.clone(),
                        vis: item.vis.clone(),
                        sig: item.sig.clone(),
                        block: Box::new(item.block.clone()),
                    });
                }
                syn::visit::visit_impl_item_fn(self, item);
            }
        }
        let mut finder = Finder { name, found: None };
        finder.visit_file(file);
        finder.found.expect("the fixture declares the target")
    }

    fn refusal(src: &str, name: &str) -> Option<String> {
        let file = syn::parse_file(src).expect("fixture parses");
        verified_refusal(Some(&file), &target(&file, name))
    }

    const D: &str =
        "pub struct D { pub a: u64 } impl Drop for D { fn drop(&mut self) { panic!(\"drop\") } } ";

    #[test]
    fn a_function_that_can_drop_a_value_with_a_destructor_is_refused() {
        for (rest, name) in [
            // A parameter, a local, an explicit `drop` and an overwrite.
            ("fn dr(d: D) {}", "dr"),
            ("fn f() { let d = D { a: 0u64 }; }", "f"),
            ("fn f(d: D) { drop(d); }", "f"),
            ("fn f(r: &mut D) { *r = D { a: 1u64 }; }", "f"),
            // A value that holds one: a field, a collection, an `Option`, an
            // alias, an enum payload.
            ("struct W { d: D } fn f(w: W) {}", "f"),
            ("fn f(v: Vec<D>) {}", "f"),
            ("fn f(o: Option<D>) {}", "f"),
            ("type A = D; fn f(a: A) {}", "f"),
            ("enum E { X(D), Y } fn f(e: E) {}", "f"),
            ("struct W { d: D } type A = Vec<W>; fn f(a: A) {}", "f"),
            // A function that produces one, directly, through a method of an
            // impl for another type, or through a callee's body.
            ("fn mk() -> D { D { a: 0u64 } } fn f() { mk(); }", "f"),
            ("fn h() -> u64 { let d = D { a: 1u64 }; 5u64 } fn f() -> u64 { h() }", "f"),
            ("struct F; impl F { fn make(&self) -> D { D { a: 0u64 } } } fn f(g: &F) { g.make(); }", "f"),
            ("fn mk() -> D { D { a: 0u64 } } #[trust_vc::requires(mk().a > 0u64)] fn f() {}", "f"),
            ("fn mk() -> D { D { a: 0u64 } } use self::mk as make; fn f() { make(); }", "f"),
            ("extern \"C\" { fn mk() -> D; } fn f() { unsafe { mk(); } }", "f"),
            // A method of an impl for the type.
            ("impl D { fn consume(self) {} }", "consume"),
            ("impl D { fn get(&self) -> u64 { self.a } }", "get"),
            // A const, a static, a trait whose signature names the type.
            ("const K: D = D { a: 1u64 }; fn f() { let _ = K; }", "f"),
            ("static S: std::sync::Mutex<Option<D>> = std::sync::Mutex::new(None); fn f() { S.lock(); }", "f"),
            ("trait Mk { fn mk() -> D; } fn f<T: Mk>() { T::mk(); }", "f"),
            // An associated type: a `for` loop and a projection reach it.
            ("struct It; impl Iterator for It { type Item = D; fn next(&mut self) -> Option<D> { None } } fn f(it: It) { for x in it {} }", "f"),
            ("trait Tr { type A; } impl<X> Tr for X { type A = D; } fn f(x: <u64 as Tr>::A) {}", "f"),
            // An operator impl of another type that drops one runs from `+`.
            ("#[derive(Clone, Copy)] struct N { v: u64 } impl std::ops::Add for N { type Output = N; fn add(self, o: N) -> N { let d = D { a: 0u64 }; N { v: self.v } } } fn f(x: N, y: N) -> N { x + y }", "f"),
        ] {
            let src = format!("{D}{rest}");
            let message = refusal(&src, name).unwrap_or_else(|| panic!("not refused: {src}"));
            assert!(message.starts_with(DROP_GLUE_TAG), "{message}");
        }
    }

    #[test]
    fn every_spelling_of_a_drop_impl_is_seen() {
        for (src, name) in [
            ("struct G<T> { t: T } impl<T> Drop for G<T> { fn drop(&mut self) {} } fn f(g: G<u64>) {}", "f"),
            ("struct R<'a> { w: &'a mut Vec<u64> } impl<'a> Drop for R<'a> { fn drop(&mut self) { self.w.clear(); } } fn f(v: &mut Vec<u64>) { let r = R { w: v }; }", "f"),
            ("mod m { pub struct D2; impl Drop for D2 { fn drop(&mut self) {} } } fn f(d: m::D2) {}", "f"),
            ("struct D3 { a: u64 } impl std::ops::Drop for D3 { fn drop(&mut self) {} } fn f(d: D3) {}", "f"),
            // Through an alias or a rename of the type.
            ("struct D3 { a: u64 } type A3 = D3; impl Drop for A3 { fn drop(&mut self) {} } fn f(d: D3) {}", "f"),
            ("mod m { pub struct S; } use m::S as T; impl Drop for T { fn drop(&mut self) {} } fn f(s: m::S) {}", "f"),
            // A variant of an enum with a destructor.
            ("enum E { A(u64), B } impl Drop for E { fn drop(&mut self) {} } use E::*; fn f() { let x = B; }", "f"),
            // An out-of-line module can implement `Drop` for a type of the file.
            ("mod other; struct P { a: u64 } fn f(p: P) {}", "f"),
        ] {
            let message = refusal(src, name).unwrap_or_else(|| panic!("not refused: {src}"));
            assert!(message.starts_with(DROP_GLUE_TAG), "{message}");
        }
    }

    #[test]
    fn a_function_that_names_no_value_with_a_destructor_is_not_refused() {
        for (src, name) in [
            // No `Drop` impl.
            ("pub struct D { pub a: u64 } fn dr(d: D) {}", "dr"),
            ("fn f<T: Drop>(t: T) {} // impl Drop for D", "f"),
            ("fn f() -> &'static str { \"impl Drop for D\" }", "f"),
        ] {
            assert_eq!(refusal(src, name), None, "{src}");
        }
        for (rest, name) in [
            ("fn f(x: u64) -> u64 { x }", "f"),
            ("struct N { a: u64 } fn f(n: N) -> u64 { n.a }", "f"),
            // A type used inside the one with a destructor holds none.
            ("struct Inner { a: u64 } struct W2 { d: D, i: Inner } fn f(i: Inner) {}", "f"),
            // A method of an impl for the type is reached only through the
            // type, so a same-named method of another type is not refused.
            ("impl D { fn get(&self) -> u64 { self.a } } struct N; impl N { fn get(&self) -> u64 { 1u64 } } fn f(n: &N) -> u64 { n.get() }", "f"),
            ("struct N; impl N { fn get(&self) -> u64 { 1u64 } }", "get"),
        ] {
            let src = format!("{D}{rest}");
            assert_eq!(refusal(&src, name), None, "{src}");
        }
    }

    #[test]
    fn a_method_the_file_does_not_show_is_refused() {
        let file = syn::parse_file(D).expect("fixture parses");
        let method: ItemFn = syn::parse_quote! { fn elsewhere(self) -> u64 { 1u64 } };
        let message = verified_refusal(Some(&file), &method).expect("refused");
        assert!(message.starts_with(DROP_GLUE_TAG), "{message}");
        let free: ItemFn = syn::parse_quote! { fn elsewhere(x: u64) -> u64 { x } };
        assert_eq!(verified_refusal(Some(&file), &free), None);
    }

    #[test]
    fn the_message_names_the_path_to_the_destructor() {
        let src = format!("{D}fn mk() -> D {{ D {{ a: 0u64 }} }} fn f() {{ mk(); }}");
        let message = refusal(&src, "f").expect("refused");
        assert!(message.contains("`mk`, which names `D`"), "{message}");
        assert!(message.contains("`impl Drop for D`"), "{message}");
    }

    #[test]
    fn trait_conformance_is_refused_where_an_impl_method_names_one() {
        let refused = syn::parse_file(&format!(
            "{D}trait Tr {{ fn m(&self) -> u64; }} struct X; impl Tr for X {{ fn m(&self) -> u64 {{ let d = D {{ a: 0u64 }}; 1u64 }} }}"
        ))
        .expect("parses");
        assert!(file_refusal(&refused).is_some());
        let kept = syn::parse_file(&format!(
            "{D}trait Tr {{ fn m(&self) -> u64; }} struct X; impl Tr for X {{ fn m(&self) -> u64 {{ 1u64 }} }}"
        ))
        .expect("parses");
        assert_eq!(file_refusal(&kept), None);
    }
}
