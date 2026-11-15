// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Which expressions of a function can hold a value of a generic type, read
//! from the syntax.
//!
//! A value whose type is a generic parameter (`t: T`, `t: &T`, `t: impl Tr`,
//! `t: &dyn Tr`, `self` in a trait) runs code this lane cannot see whenever a
//! method is called on it or it is compared: the impl is chosen by the
//! caller. The lane reads such a method call as one application of one
//! function symbol and `==` on such values as structural equality. Neither
//! holds for every impl: a method can read a `Cell` or a counter, and a
//! `PartialEq` impl need not be reflexive (`f64::NAN != f64::NAN`).
//!
//! [`GenericScope`] classifies the expressions of one function:
//!
//! * [`Kind::Generic`]: the value may itself be of a generic type, so a
//!   method call on it is a call of an impl this lane cannot see;
//! * [`Kind::Contains`]: the value's type mentions a generic type (`Vec<T>`,
//!   `(T, T)`, `Option<T>`), so comparing it compares generic values, and a
//!   projection of it (`p.0`, `v[i]`) may be generic;
//! * [`Kind::Concrete`] — neither.
//!
//! The reading is syntactic and errs toward the generic side: a local takes
//! the kind of what initializes it, merged over every binding of its name, an
//! untyped closure parameter is generic, and a call whose result type is not
//! known is generic when anything it is given is. Erring that way only makes
//! the rules that use it refuse more.

use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use syn::visit::Visit;
use syn::{Expr, File, Signature, Type};

/// How much of a generic type an expression's value may carry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Kind {
    Concrete,
    Contains,
    Generic,
}

/// Std methods whose result is a primitive or a std type with no type
/// parameter, whatever the receiver. A method the file declares is read from
/// its declarations instead.
const STD_CONCRETE_RESULT_METHODS: &[&str] = &[
    "len",
    "is_empty",
    "is_some",
    "is_none",
    "is_ok",
    "is_err",
    "contains",
    "contains_key",
    "capacity",
    "count",
    "starts_with",
    "ends_with",
    "eq",
    "ne",
    "lt",
    "le",
    "gt",
    "ge",
    "cmp",
    "partial_cmp",
    "to_string",
    "all",
    "any",
    "position",
];

/// Std methods that hand out an element, the contents or the target of their
/// receiver (`o.unwrap()`, `v.first()`, `b.as_ref()`), so on a value whose
/// type mentions a generic type their result may itself be generic. Any other
/// std method on such a value returns a value whose type mentions it
/// (`a.add(b)` on a `Multiset<V>`).
const ELEMENT_METHODS: &[&str] = &[
    "unwrap",
    "expect",
    "unwrap_or",
    "unwrap_or_else",
    "unwrap_or_default",
    "unwrap_unchecked",
    "unwrap_err",
    "expect_err",
    "get_Some_0",
    "get_Ok_0",
    "get_Err_0",
    "index",
    "index_mut",
    "spec_index",
    "first",
    "last",
    "first_mut",
    "last_mut",
    "pop",
    "pop_front",
    "pop_back",
    "remove",
    "swap_remove",
    "take",
    "replace",
    "get",
    "get_mut",
    "get_unchecked",
    "choose",
    "next",
    "next_back",
    "nth",
    "peek",
    "front",
    "back",
    "min",
    "max",
    "min_by",
    "max_by",
    "min_by_key",
    "max_by_key",
    "fold",
    "reduce",
    "sum",
    "product",
    "find",
    "find_map",
    "as_ref",
    "as_mut",
    "as_deref",
    "borrow",
    "borrow_mut",
    "deref",
    "deref_mut",
    "into_inner",
    "call",
    "call_mut",
    "call_once",
];

/// Collection types whose methods other than [`ELEMENT_METHODS`] return a
/// collection, a primitive or nothing, whatever they are given (`s.insert(x)`
/// on a `Multiset<V>`), unlike `Option::insert(x)`, which hands back `&mut x`.
const COLLECTIONS: &[&str] = &[
    "Vec", "VecDeque", "HashSet", "HashMap", "BTreeSet", "BTreeMap", "Seq", "Set", "Map",
    "Multiset",
];

/// Smart pointers a method call dereferences through, so `Box<T>` is as
/// generic as `T` for a method receiver.
const SMART_POINTERS: &[&str] = &["Box", "Rc", "Arc"];

/// What the file's own declarations say about each function and method name.
#[derive(Default)]
pub(super) struct FileDecls {
    /// For each declared function, method and trait method name, the most
    /// generic kind any declaration of it returns.
    returns: BTreeMap<String, Kind>,
    /// The same with `Self` read as a concrete type, which it is for a
    /// method called on a concrete receiver.
    returns_on_concrete: BTreeMap<String, Kind>,
    /// Names every declaration of which is a spec function.
    spec_names: BTreeSet<String>,
    /// Names every declaration of which is a free function whose return type
    /// is generic only in its own type parameters, each of which its
    /// parameter types name, so a call's arguments instantiate it.
    returns_from_arguments: BTreeSet<String>,
    /// Names of the `struct`s, `enum`s, `union`s and type aliases the file
    /// declares.
    type_names: BTreeSet<String>,
}

impl FileDecls {
    pub(super) fn new(file: Option<&File>) -> Self {
        Self::with_opaque(file, &BTreeSet::new())
    }

    /// Like [`FileDecls::new`], reading the type names in `opaque` as
    /// generic type parameters wherever they appear.
    pub(super) fn with_opaque(file: Option<&File>, opaque: &BTreeSet<String>) -> Self {
        let mut collector = DeclCollector {
            opaque: opaque.clone(),
            ..DeclCollector::default()
        };
        if let Some(file) = file {
            collector.visit_file(file);
        }
        let mut decls = FileDecls {
            type_names: collector.type_names,
            ..FileDecls::default()
        };
        for (name, entries) in collector.entries {
            let kind = entries
                .iter()
                .map(|entry| entry.returns)
                .max()
                .unwrap_or(Kind::Concrete);
            if entries.iter().all(|entry| entry.spec) {
                decls.spec_names.insert(name.clone());
            }
            if entries.iter().all(|entry| entry.from_arguments) {
                decls.returns_from_arguments.insert(name.clone());
            }
            let on_concrete = entries
                .iter()
                .map(|entry| entry.returns_on_concrete)
                .max()
                .unwrap_or(Kind::Concrete);
            decls.returns_on_concrete.insert(name.clone(), on_concrete);
            decls.returns.insert(name, kind);
        }
        decls
    }

    /// The kind a call of the file's function or method `name` returns, or
    /// `None` when the file declares no such name.
    fn declared_return(&self, name: &str) -> Option<Kind> {
        self.returns.get(name).copied()
    }

    /// The kind a call of the file's method `name` on a concrete receiver
    /// returns, or `None` when the file declares no such name.
    fn declared_return_on_concrete(&self, name: &str) -> Option<Kind> {
        self.returns_on_concrete.get(name).copied()
    }

    /// True when the file declares `name` only as spec functions, which are
    /// functions of their arguments by declaration.
    pub(super) fn is_spec_only(&self, name: &str) -> bool {
        self.spec_names.contains(name)
    }

    /// True when a call of `name` returns a value as generic as its
    /// arguments (see `returns_from_arguments`).
    fn returns_from_arguments(&self, name: &str) -> bool {
        self.returns_from_arguments.contains(name)
    }
}

struct DeclEntry {
    returns: Kind,
    returns_on_concrete: Kind,
    spec: bool,
    /// The return type is generic only in the function's own type
    /// parameters, and its parameter types name each of them.
    from_arguments: bool,
}

#[derive(Default)]
struct DeclCollector {
    /// Type names read as generic type parameters everywhere.
    opaque: BTreeSet<String>,
    params: Vec<BTreeSet<String>>,
    self_kinds: Vec<Kind>,
    entries: BTreeMap<String, Vec<DeclEntry>>,
    type_names: BTreeSet<String>,
}

impl DeclCollector {
    fn record(&mut self, attrs: &[syn::Attribute], sig: &Signature) {
        let mut outer: BTreeSet<String> = self.params.iter().flatten().cloned().collect();
        outer.extend(self.opaque.iter().cloned());
        let own = type_param_names(&sig.generics);
        let mut params = outer.clone();
        params.extend(own.iter().cloned());
        let self_kind = self.self_kinds.last().copied().unwrap_or(Kind::Concrete);
        let (returns, returns_on_concrete, from_arguments) = match &sig.output {
            syn::ReturnType::Default => (Kind::Concrete, Kind::Concrete, true),
            syn::ReturnType::Type(_, ty) => {
                let inputs = sig.inputs.to_token_stream();
                let from_arguments = self.self_kinds.is_empty()
                    && type_kind(ty, &outer, self_kind) == Kind::Concrete
                    && own.iter().all(|param| {
                        !mentions_name(&ty.to_token_stream(), param)
                            || mentions_name(&inputs, param)
                    });
                (
                    type_kind(ty, &params, self_kind),
                    type_kind(ty, &params, Kind::Concrete),
                    from_arguments,
                )
            }
        };
        let spec = crate::mode_attrs::classify_attrs(attrs) == crate::mode::FunctionMode::Spec;
        self.entries
            .entry(unraw(&sig.ident))
            .or_default()
            .push(DeclEntry {
                returns,
                returns_on_concrete,
                spec,
                from_arguments,
            });
    }
}

impl<'ast> Visit<'ast> for DeclCollector {
    fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
        self.type_names.insert(unraw(&item.ident));
        syn::visit::visit_item_struct(self, item);
    }

    fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
        self.type_names.insert(unraw(&item.ident));
        syn::visit::visit_item_enum(self, item);
    }

    fn visit_item_union(&mut self, item: &'ast syn::ItemUnion) {
        self.type_names.insert(unraw(&item.ident));
        syn::visit::visit_item_union(self, item);
    }

    fn visit_item_type(&mut self, item: &'ast syn::ItemType) {
        self.type_names.insert(unraw(&item.ident));
        syn::visit::visit_item_type(self, item);
    }

    fn visit_item_mod(&mut self, module: &'ast syn::ItemMod) {
        let params = std::mem::take(&mut self.params);
        let kinds = std::mem::take(&mut self.self_kinds);
        syn::visit::visit_item_mod(self, module);
        self.params = params;
        self.self_kinds = kinds;
    }

    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        let params = type_param_names(&item.generics);
        let mut kind_params = params.clone();
        kind_params.extend(self.opaque.iter().cloned());
        let kind = type_kind(&item.self_ty, &kind_params, Kind::Concrete);
        self.params.push(params);
        self.self_kinds.push(kind);
        syn::visit::visit_item_impl(self, item);
        self.self_kinds.pop();
        self.params.pop();
    }

    fn visit_item_trait(&mut self, item: &'ast syn::ItemTrait) {
        self.params.push(type_param_names(&item.generics));
        self.self_kinds.push(Kind::Generic);
        syn::visit::visit_item_trait(self, item);
        self.self_kinds.pop();
        self.params.pop();
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        self.record(&item.attrs, &item.sig);
        let params = std::mem::take(&mut self.params);
        let kinds = std::mem::take(&mut self.self_kinds);
        syn::visit::visit_item_fn(self, item);
        self.params = params;
        self.self_kinds = kinds;
    }

    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        self.record(&item.attrs, &item.sig);
        let params = std::mem::take(&mut self.params);
        let kinds = std::mem::take(&mut self.self_kinds);
        syn::visit::visit_impl_item_fn(self, item);
        self.params = params;
        self.self_kinds = kinds;
    }

    fn visit_trait_item_fn(&mut self, item: &'ast syn::TraitItemFn) {
        self.record(&item.attrs, &item.sig);
        let params = std::mem::take(&mut self.params);
        let kinds = std::mem::take(&mut self.self_kinds);
        syn::visit::visit_trait_item_fn(self, item);
        self.params = params;
        self.self_kinds = kinds;
    }
}

/// The generic context a function is declared in: the type parameters of
/// its enclosing `impl` or `trait`, and the kind of `Self` there (generic in
/// a trait).
#[derive(Clone, Default)]
pub(super) struct OuterContext {
    pub(super) type_params: BTreeSet<String>,
    pub(super) self_kind: Option<Kind>,
    /// The kind of `Self` with the file's opaque type names read as generic
    /// (see `runtime_checked_clauses::opaque_type_names`).
    pub(super) opaque_self_kind: Option<Kind>,
}

impl OuterContext {
    pub(super) fn merge(&mut self, other: &OuterContext) {
        self.type_params.extend(other.type_params.iter().cloned());
        self.self_kind = max_kind(self.self_kind, other.self_kind);
        self.opaque_self_kind = max_kind(self.opaque_self_kind, other.opaque_self_kind);
    }
}

fn max_kind(a: Option<Kind>, b: Option<Kind>) -> Option<Kind> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.max(b)),
        (a, b) => a.or(b),
    }
}

/// The kinds of the names one function binds.
pub(super) struct GenericScope<'d> {
    decls: &'d FileDecls,
    type_params: BTreeSet<String>,
    self_kind: Kind,
    names: BTreeMap<String, Kind>,
    /// For each parameter whose type is exactly a generic type, `T`, `&T`,
    /// `impl Tr` or `Self` in a trait, a name for that type: the parameter
    /// name for `impl Tr`, which is a type of its own.
    receiver_types: BTreeMap<String, String>,
    /// Names the body binds again with `let`, a pattern, a closure parameter
    /// or an assignment.
    rebound: BTreeSet<String>,
    /// Names whose every binding holds one of the [`COLLECTIONS`].
    collections: BTreeSet<String>,
    /// For each parameter of a callable type (`f: F` with `F: Fn() -> u64`,
    /// `f: impl Fn() -> u64`, `f: fn() -> u64`), the kind of what calling it
    /// returns.
    callable_outputs: BTreeMap<String, Kind>,
}

impl<'d> GenericScope<'d> {
    /// The scope of a function with signature `sig` and body `block`, or
    /// `None` when nothing in its signature or context is generic.
    pub(super) fn new(
        decls: &'d FileDecls,
        outer: &OuterContext,
        sig: &Signature,
        block: Option<&syn::Block>,
    ) -> Option<Self> {
        let mut type_params = outer.type_params.clone();
        type_params.extend(type_param_names(&sig.generics));
        let self_kind = outer.self_kind.unwrap_or(Kind::Concrete);
        let mut scope = GenericScope {
            decls,
            type_params,
            self_kind,
            names: BTreeMap::new(),
            receiver_types: BTreeMap::new(),
            rebound: BTreeSet::new(),
            collections: BTreeSet::new(),
            callable_outputs: BTreeMap::new(),
        };
        for input in &sig.inputs {
            match input {
                syn::FnArg::Receiver(receiver) => {
                    scope.bind("self", self_kind);
                    if self_kind == Kind::Generic && receiver.colon_token.is_none() {
                        scope
                            .receiver_types
                            .insert("self".to_string(), "Self".to_string());
                    }
                }
                syn::FnArg::Typed(typed) => {
                    let kind = scope.type_kind(&typed.ty);
                    scope.bind_pat(&typed.pat, kind);
                    if let syn::Pat::Ident(ident) = &*typed.pat {
                        let name = unraw(&ident.ident);
                        if scope.is_collection_type(&typed.ty) {
                            scope.collections.insert(name.clone());
                        }
                        if let Some(ty) = scope.exact_generic_type(&typed.ty, &name) {
                            scope.receiver_types.insert(name, ty);
                        }
                    }
                    if let (syn::Pat::Ident(ident), Some(output)) =
                        (&*typed.pat, scope.callable_output(&typed.ty, &sig.generics))
                    {
                        scope.callable_outputs.insert(unraw(&ident.ident), output);
                    }
                }
            }
        }
        if let syn::ReturnType::Type(_, ty) = &sig.output {
            let kind = scope.type_kind(ty);
            scope.bind("result", kind);
        }
        let generic_context = !scope.type_params.is_empty()
            || self_kind != Kind::Concrete
            || scope.names.values().any(|kind| *kind != Kind::Concrete)
            || block.is_some_and(|block| names_impl_or_dyn(&block.to_token_stream()));
        if !generic_context {
            return None;
        }
        if let Some(block) = block {
            let mut sites = BindingSites::default();
            sites.visit_block(block);
            scope.rebound = sites
                .sites
                .iter()
                .flat_map(|site| site.names.iter().cloned())
                .collect();
            // A name stays a collection only when every binding of it is one.
            // The reading is not monotone, so it gives up, keeping no local
            // collection, when it does not settle.
            let params = scope.collections.clone();
            let mut settled = false;
            for _ in 0..16 {
                let before = scope.collections.clone();
                let rebound_elsewhere: BTreeSet<String> = sites
                    .sites
                    .iter()
                    .filter(|site| {
                        site.destructured
                            || !match &site.source {
                                BindingSource::Init(expr) => scope.collection_rooted(expr),
                                BindingSource::Type(ty) => scope.is_collection_type(ty),
                                BindingSource::Scrutinee(_) | BindingSource::Unknown => false,
                            }
                    })
                    .flat_map(|site| site.names.iter().cloned())
                    .collect();
                let bound_as_collection: BTreeSet<String> = sites
                    .sites
                    .iter()
                    .filter(|site| {
                        !site.destructured
                            && match &site.source {
                                BindingSource::Init(expr) => scope.collection_rooted(expr),
                                BindingSource::Type(ty) => scope.is_collection_type(ty),
                                BindingSource::Scrutinee(_) | BindingSource::Unknown => false,
                            }
                    })
                    .flat_map(|site| site.names.iter().cloned())
                    .collect();
                scope.collections.extend(bound_as_collection);
                scope
                    .collections
                    .retain(|name| !rebound_elsewhere.contains(name));
                if scope.collections == before {
                    settled = true;
                    break;
                }
            }
            if !settled {
                scope.collections = params
                    .into_iter()
                    .filter(|name| !scope.rebound.contains(name))
                    .collect();
            }
            loop {
                let before = scope.names.clone();
                for site in &sites.sites {
                    let kind = match &site.source {
                        BindingSource::Init(expr) => scope.expr_kind(expr),
                        BindingSource::Type(ty) => scope.type_kind(ty),
                        BindingSource::Scrutinee(expr) => {
                            if scope.expr_kind(expr) == Kind::Concrete {
                                Kind::Concrete
                            } else {
                                Kind::Generic
                            }
                        }
                        BindingSource::Unknown => Kind::Generic,
                    };
                    let kind = if site.destructured && kind == Kind::Contains {
                        Kind::Generic
                    } else {
                        kind
                    };
                    for name in &site.names {
                        scope.bind(name, kind);
                    }
                }
                if scope.names == before {
                    break;
                }
            }
        }
        Some(scope)
    }

    /// A name for `ty` when it is exactly a generic type behind references:
    /// a type parameter, or `impl Tr`, which is a type of its own named after
    /// the parameter `param`.
    fn exact_generic_type(&self, ty: &Type, param: &str) -> Option<String> {
        match ty {
            Type::Reference(reference) => self.exact_generic_type(&reference.elem, param),
            Type::Paren(paren) => self.exact_generic_type(&paren.elem, param),
            Type::Group(group) => self.exact_generic_type(&group.elem, param),
            Type::ImplTrait(_) => Some(format!("impl {param}")),
            Type::Path(path) if path.qself.is_none() => {
                let name = unraw(path.path.get_ident()?);
                self.type_params.contains(&name).then_some(name)
            }
            _ => None,
        }
    }

    /// The generic type of `receiver` when it is a parameter whose type is
    /// exactly a generic type, read through `&`, `*` and parentheses.
    pub(super) fn receiver_type(&self, receiver: &Expr) -> Option<String> {
        match receiver {
            Expr::Paren(inner) => self.receiver_type(&inner.expr),
            Expr::Group(inner) => self.receiver_type(&inner.expr),
            Expr::Reference(inner) => self.receiver_type(&inner.expr),
            Expr::Unary(inner) if matches!(inner.op, syn::UnOp::Deref(_)) => {
                self.receiver_type(&inner.expr)
            }
            Expr::Path(path) if path.qself.is_none() => {
                let name = unraw(path.path.get_ident()?);
                // A parameter rebound anywhere in the body may hold another
                // value, so it is read as any receiver.
                if self.rebound.contains(&name) {
                    return None;
                }
                self.receiver_types.get(&name).cloned()
            }
            _ => None,
        }
    }

    /// The kind of what a value of type `ty` returns when called, when `ty`
    /// is callable: an `Fn`, `FnMut` or `FnOnce` bound written on the type,
    /// on a type parameter in `generics`, or a `fn` pointer.
    fn callable_output(&self, ty: &Type, generics: &syn::Generics) -> Option<Kind> {
        match ty {
            Type::Reference(reference) => self.callable_output(&reference.elem, generics),
            Type::Paren(paren) => self.callable_output(&paren.elem, generics),
            Type::Group(group) => self.callable_output(&group.elem, generics),
            Type::BareFn(bare) => Some(self.return_kind(&bare.output)),
            Type::ImplTrait(item) => self.bounds_output(item.bounds.iter()),
            Type::TraitObject(item) => self.bounds_output(item.bounds.iter()),
            Type::Path(path) if path.qself.is_none() => {
                let last = path.path.segments.last()?;
                if SMART_POINTERS.contains(&unraw(&last.ident).as_str()) {
                    if let syn::PathArguments::AngleBracketed(args) = &last.arguments {
                        return args.args.iter().find_map(|arg| match arg {
                            syn::GenericArgument::Type(inner) => {
                                self.callable_output(inner, generics)
                            }
                            _ => None,
                        });
                    }
                    return None;
                }
                let name = unraw(path.path.get_ident()?);
                let own = generics
                    .type_params()
                    .filter(|param| param.ident == name)
                    .flat_map(|param| param.bounds.iter());
                let clauses = generics
                    .where_clause
                    .iter()
                    .flat_map(|clause| clause.predicates.iter())
                    .filter_map(|predicate| match predicate {
                        syn::WherePredicate::Type(predicate)
                            if predicate.bounded_ty.to_token_stream().to_string() == name =>
                        {
                            Some(predicate.bounds.iter())
                        }
                        _ => None,
                    })
                    .flatten();
                self.bounds_output(own.chain(clauses))
            }
            _ => None,
        }
    }

    fn bounds_output<'b>(
        &self,
        bounds: impl Iterator<Item = &'b syn::TypeParamBound>,
    ) -> Option<Kind> {
        bounds
            .filter_map(|bound| match bound {
                syn::TypeParamBound::Trait(bound) => bound.path.segments.last(),
                _ => None,
            })
            .find_map(|segment| {
                let name = unraw(&segment.ident);
                if !matches!(name.as_str(), "Fn" | "FnMut" | "FnOnce") {
                    return None;
                }
                match &segment.arguments {
                    syn::PathArguments::Parenthesized(args) => Some(self.return_kind(&args.output)),
                    _ => Some(Kind::Generic),
                }
            })
    }

    fn return_kind(&self, output: &syn::ReturnType) -> Kind {
        match output {
            syn::ReturnType::Default => Kind::Concrete,
            syn::ReturnType::Type(_, ty) => self.type_kind(ty),
        }
    }

    fn bind(&mut self, name: &str, kind: Kind) {
        let entry = self.names.entry(name.to_string()).or_insert(kind);
        *entry = (*entry).max(kind);
    }

    fn bind_pat(&mut self, pat: &syn::Pat, kind: Kind) {
        let destructured = !matches!(pat, syn::Pat::Ident(_));
        let kind = if destructured && kind == Kind::Contains {
            Kind::Generic
        } else {
            kind
        };
        let mut names = PatNames::default();
        names.visit_pat(pat);
        for name in names.names {
            self.bind(&name, kind);
        }
    }

    fn type_kind(&self, ty: &Type) -> Kind {
        type_kind(ty, &self.type_params, self.self_kind)
    }

    /// The kind of the value `expr` evaluates to.
    pub(super) fn expr_kind(&self, expr: &Expr) -> Kind {
        match expr {
            Expr::Lit(_) | Expr::Cast(_) => Kind::Concrete,
            Expr::Path(path) => self.path_kind(path),
            Expr::Paren(inner) => self.expr_kind(&inner.expr),
            Expr::Group(inner) => self.expr_kind(&inner.expr),
            Expr::Reference(inner) => self.expr_kind(&inner.expr),
            Expr::Unary(inner) => self.expr_kind(&inner.expr),
            Expr::Field(field) => projection(self.expr_kind(&field.base)),
            Expr::Index(index) => projection(self.expr_kind(&index.expr)),
            Expr::MethodCall(call) => {
                let method = unraw(&call.method);
                let receiver = self.expr_kind(&call.receiver);
                let given = call
                    .args
                    .iter()
                    .map(|arg| self.expr_kind(arg))
                    .max()
                    .unwrap_or(Kind::Concrete);
                let turbofish = call
                    .turbofish
                    .as_ref()
                    .is_some_and(|turbofish| self.tokens_mention(&turbofish.to_token_stream()));
                let declared = self.decls.declared_return(&method);
                if declared.is_none() && STD_CONCRETE_RESULT_METHODS.contains(&method.as_str()) {
                    return Kind::Concrete;
                }
                if turbofish {
                    return Kind::Generic;
                }
                match receiver {
                    // Only a trait method can be called on a generic value; the
                    // file's declaration of that name says what it returns.
                    Kind::Generic => declared.unwrap_or(Kind::Generic),
                    // A std method of a container may hand out an element; a
                    // method of the file may return what its declaration says.
                    Kind::Contains => {
                        let std_result = if ELEMENT_METHODS.contains(&method.as_str())
                            || (given == Kind::Generic && !self.collection_rooted(&call.receiver))
                        {
                            Kind::Generic
                        } else {
                            Kind::Contains
                        };
                        std_result.max(declared.unwrap_or(Kind::Concrete))
                    }
                    // `Self` is the receiver's concrete type in whichever
                    // declaration the call resolves to.
                    Kind::Concrete => given.max(
                        self.decls
                            .declared_return_on_concrete(&method)
                            .unwrap_or(Kind::Concrete),
                    ),
                }
            }
            Expr::Call(call) => self.call_kind(call),
            Expr::Tuple(tuple) => aggregate(tuple.elems.iter().map(|elem| self.expr_kind(elem))),
            Expr::Array(array) => aggregate(array.elems.iter().map(|elem| self.expr_kind(elem))),
            Expr::Repeat(repeat) => aggregate(std::iter::once(self.expr_kind(&repeat.expr))),
            Expr::Struct(item) => {
                let fields = aggregate(
                    item.fields
                        .iter()
                        .map(|field| self.expr_kind(&field.expr))
                        .chain(item.rest.iter().map(|rest| self.expr_kind(rest))),
                );
                if self.tokens_mention(&item.path.to_token_stream()) {
                    fields.max(Kind::Contains)
                } else {
                    fields
                }
            }
            Expr::Range(range) => aggregate(
                range
                    .start
                    .iter()
                    .chain(range.end.iter())
                    .map(|end| self.expr_kind(end)),
            ),
            Expr::Binary(binary) => {
                if is_comparison(&binary.op) || is_logical(&binary.op) {
                    Kind::Concrete
                } else {
                    self.expr_kind(&binary.left)
                        .max(self.expr_kind(&binary.right))
                }
            }
            other => {
                if self.tokens_mention(&other.to_token_stream()) {
                    Kind::Generic
                } else {
                    Kind::Concrete
                }
            }
        }
    }

    /// True when `ty` is, behind references, one of the [`COLLECTIONS`] and
    /// not a type of the file spelled like one.
    fn is_collection_type(&self, ty: &Type) -> bool {
        match ty {
            Type::Reference(reference) => self.is_collection_type(&reference.elem),
            Type::Paren(paren) => self.is_collection_type(&paren.elem),
            Type::Group(group) => self.is_collection_type(&group.elem),
            Type::Path(path) if path.qself.is_none() => {
                path.path.segments.last().is_some_and(|last| {
                    let name = unraw(&last.ident);
                    COLLECTIONS.contains(&name.as_str()) && !self.decls.type_names.contains(&name)
                })
            }
            _ => false,
        }
    }

    /// True when `expr` holds one of the [`COLLECTIONS`]: a name bound only to
    /// one, a constructor path on one (`Multiset::<V>::empty()`), or a
    /// method of one other than an [`ELEMENT_METHODS`] method.
    fn collection_rooted(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Paren(inner) => self.collection_rooted(&inner.expr),
            Expr::Group(inner) => self.collection_rooted(&inner.expr),
            Expr::Reference(inner) => self.collection_rooted(&inner.expr),
            Expr::Path(path) if path.qself.is_none() => path
                .path
                .get_ident()
                .is_some_and(|ident| self.collections.contains(&unraw(ident))),
            Expr::Call(call) => match &*call.func {
                Expr::Path(path) if path.qself.is_none() && path.path.segments.len() >= 2 => {
                    let owner = unraw(&path.path.segments[path.path.segments.len() - 2].ident);
                    COLLECTIONS.contains(&owner.as_str()) && !self.decls.type_names.contains(&owner)
                }
                _ => false,
            },
            Expr::MethodCall(call) => {
                !ELEMENT_METHODS.contains(&unraw(&call.method).as_str())
                    && self.decls.declared_return(&unraw(&call.method)).is_none()
                    && self.collection_rooted(&call.receiver)
            }
            _ => false,
        }
    }

    /// The kind of the value a call `f(args)` returns.
    fn call_kind(&self, call: &syn::ExprCall) -> Kind {
        let given = call
            .args
            .iter()
            .map(|arg| self.expr_kind(arg))
            .max()
            .unwrap_or(Kind::Concrete);
        let Expr::Path(path) = &*call.func else {
            return if given != Kind::Concrete || self.tokens_mention(&call.func.to_token_stream()) {
                Kind::Generic
            } else {
                Kind::Concrete
            };
        };
        // `<u32 as Default>::default()` returns a value of a concrete type
        // when the type it names is concrete.
        if let Some(qself) = &path.qself {
            if self.type_kind(&qself.ty) != Kind::Concrete {
                return Kind::Generic;
            }
        }
        if let Some(ident) = path.path.get_ident() {
            if let Some(kind) = self.callable_outputs.get(&unraw(ident)) {
                return *kind;
            }
            if self.name_kind(&unraw(ident)) != Kind::Concrete {
                return Kind::Generic;
            }
        }
        let segments = &path.path.segments;
        if segments
            .first()
            .is_some_and(|first| self.is_generic_type_name(&unraw(&first.ident)))
        {
            return Kind::Generic;
        }
        if let Some(last) = segments.last() {
            let name = unraw(&last.ident);
            if let Some(kind) = self.decls.declared_return(&name) {
                // A free function generic only in its own parameters returns
                // what its arguments or turbofish instantiate it with.
                if self.decls.returns_from_arguments(&name) {
                    return if given != Kind::Concrete
                        || self.tokens_mention(&path.to_token_stream())
                    {
                        Kind::Generic
                    } else {
                        Kind::Concrete
                    };
                }
                return kind;
            }
        }
        // A std or foreign function may return what it is given
        // (`std::mem::take(&mut t)`), or build a value around it
        // (`Multiset::<V>::empty()`, `Some(x)`).
        if given == Kind::Generic {
            Kind::Generic
        } else if given == Kind::Contains || self.tokens_mention(&path.to_token_stream()) {
            Kind::Contains
        } else {
            Kind::Concrete
        }
    }

    fn path_kind(&self, path: &syn::ExprPath) -> Kind {
        if let Some(qself) = &path.qself {
            if self.type_kind(&qself.ty) != Kind::Concrete {
                return Kind::Generic;
            }
        }
        let segments = &path.path.segments;
        if let Some(ident) = path.path.get_ident() {
            return self
                .names
                .get(&unraw(ident))
                .copied()
                .unwrap_or(Kind::Concrete);
        }
        match segments.first() {
            Some(first) if self.is_generic_type_name(&unraw(&first.ident)) => Kind::Generic,
            _ => Kind::Concrete,
        }
    }

    /// The kind of the local, parameter or `self` spelled `name`.
    pub(super) fn name_kind(&self, name: &str) -> Kind {
        self.names.get(name).copied().unwrap_or(Kind::Concrete)
    }

    /// True when `name` names a generic type here: a type parameter, or
    /// `Self` where `Self` is not a concrete type.
    fn is_generic_type_name(&self, name: &str) -> bool {
        self.type_params.contains(name) || (name == "Self" && self.self_kind != Kind::Concrete)
    }

    /// The method a path call `path(args)` calls on a generic type, when the
    /// path names one: `T::make()`, `Self::make()` in a trait,
    /// `<T as Tr>::make()`, or `Tr::read(&t)` whose first argument is
    /// generic.
    pub(super) fn generic_path_method(
        &self,
        path: &syn::ExprPath,
        first_arg: Option<&Expr>,
    ) -> Option<String> {
        let last = path.path.segments.last()?;
        let method = unraw(&last.ident);
        if let Some(qself) = &path.qself {
            return (self.type_kind(&qself.ty) != Kind::Concrete).then_some(method);
        }
        if path.path.segments.len() < 2 {
            return None;
        }
        let first = unraw(&path.path.segments[0].ident);
        if self.is_generic_type_name(&first) {
            return Some(method);
        }
        // `Tr::read(&t)`: a trait path, not a type of the file, whose first
        // argument is a generic place.
        let owner = unraw(&path.path.segments[path.path.segments.len() - 2].ident);
        (!self.decls.type_names.contains(&owner)
            && first_arg.is_some_and(|arg| is_place(arg) && self.expr_kind(arg) == Kind::Generic))
        .then_some(method)
    }

    /// True when `tokens` name a generic type or a name whose value is not
    /// concrete.
    pub(super) fn tokens_mention(&self, tokens: &TokenStream) -> bool {
        tokens.clone().into_iter().any(|tree| match tree {
            TokenTree::Ident(ident) => {
                let name = syn::ext::IdentExt::unraw(&ident).to_string();
                self.is_generic_type_name(&name)
                    || name == "impl"
                    || name == "dyn"
                    || self
                        .names
                        .get(&name)
                        .is_some_and(|kind| *kind != Kind::Concrete)
            }
            TokenTree::Group(group) => self.tokens_mention(&group.stream()),
            TokenTree::Punct(_) | TokenTree::Literal(_) => false,
        })
    }
}

/// True when `tokens` hold `impl` or `dyn`, which a body uses to name a type
/// whose impl it does not choose (`let b: Box<dyn Tr> = ..;`).
fn names_impl_or_dyn(tokens: &TokenStream) -> bool {
    tokens.clone().into_iter().any(|tree| match tree {
        TokenTree::Ident(ident) => ident == "impl" || ident == "dyn",
        TokenTree::Group(group) => names_impl_or_dyn(&group.stream()),
        TokenTree::Punct(_) | TokenTree::Literal(_) => false,
    })
}

/// True for an expression that names a place or a borrow of one: a path, a
/// field, an index, a dereference or a method call result.
fn is_place(expr: &Expr) -> bool {
    match expr {
        Expr::Path(_) | Expr::Field(_) | Expr::Index(_) | Expr::MethodCall(_) => true,
        Expr::Paren(inner) => is_place(&inner.expr),
        Expr::Group(inner) => is_place(&inner.expr),
        Expr::Reference(inner) => is_place(&inner.expr),
        Expr::Unary(inner) => is_place(&inner.expr),
        _ => false,
    }
}

/// The kind of a field or element of a value of kind `base`.
fn projection(base: Kind) -> Kind {
    if base == Kind::Concrete {
        Kind::Concrete
    } else {
        Kind::Generic
    }
}

/// The kind of a tuple, array or struct built from parts of the given kinds.
fn aggregate(parts: impl Iterator<Item = Kind>) -> Kind {
    if parts.max().unwrap_or(Kind::Concrete) == Kind::Concrete {
        Kind::Concrete
    } else {
        Kind::Contains
    }
}

pub(super) fn is_comparison(op: &syn::BinOp) -> bool {
    matches!(
        op,
        syn::BinOp::Eq(_)
            | syn::BinOp::Ne(_)
            | syn::BinOp::Lt(_)
            | syn::BinOp::Le(_)
            | syn::BinOp::Gt(_)
            | syn::BinOp::Ge(_)
    )
}

fn is_logical(op: &syn::BinOp) -> bool {
    matches!(op, syn::BinOp::And(_) | syn::BinOp::Or(_))
}

/// The kind of a value of type `ty`, where `type_params` are the generic
/// type parameters in scope and `self_kind` is the kind of `Self`.
pub(super) fn type_kind(ty: &Type, type_params: &BTreeSet<String>, self_kind: Kind) -> Kind {
    match ty {
        Type::Reference(reference) => type_kind(&reference.elem, type_params, self_kind),
        Type::Paren(paren) => type_kind(&paren.elem, type_params, self_kind),
        Type::Group(group) => type_kind(&group.elem, type_params, self_kind),
        Type::ImplTrait(_) | Type::TraitObject(_) => Kind::Generic,
        Type::Path(path) => {
            // `<S as Tr>::X` names one type when `S` and the trait's
            // arguments are concrete.
            if let Some(qself) = &path.qself {
                if type_kind(&qself.ty, type_params, self_kind) != Kind::Concrete
                    || mention_kind(&path.path.to_token_stream(), type_params, self_kind)
                        != Kind::Concrete
                {
                    return Kind::Generic;
                }
                return Kind::Concrete;
            }
            let segments = &path.path.segments;
            if let Some(first) = segments.first() {
                let first_name = unraw(&first.ident);
                if type_params.contains(&first_name) {
                    return Kind::Generic;
                }
                if first_name == "Self" {
                    let tail: TokenStream = segments
                        .iter()
                        .skip(1)
                        .map(ToTokens::to_token_stream)
                        .collect();
                    return if segments.len() > 1
                        && (self_kind != Kind::Concrete
                            || mention_kind(&tail, type_params, self_kind) != Kind::Concrete)
                    {
                        Kind::Generic
                    } else {
                        self_kind
                    };
                }
            }
            if let Some(last) = segments.last() {
                if SMART_POINTERS.contains(&unraw(&last.ident).as_str()) {
                    if let syn::PathArguments::AngleBracketed(args) = &last.arguments {
                        let inner = args.args.iter().find_map(|arg| match arg {
                            syn::GenericArgument::Type(inner) => Some(inner),
                            _ => None,
                        });
                        if inner.is_some_and(|inner| {
                            type_kind(inner, type_params, self_kind) == Kind::Generic
                        }) {
                            return Kind::Generic;
                        }
                    }
                }
            }
            mention_kind(&ty.to_token_stream(), type_params, self_kind)
        }
        other => mention_kind(&other.to_token_stream(), type_params, self_kind),
    }
}

fn mention_kind(tokens: &TokenStream, type_params: &BTreeSet<String>, self_kind: Kind) -> Kind {
    fn mentions(tokens: &TokenStream, type_params: &BTreeSet<String>, self_kind: Kind) -> bool {
        tokens.clone().into_iter().any(|tree| match tree {
            TokenTree::Ident(ident) => {
                let name = syn::ext::IdentExt::unraw(&ident).to_string();
                type_params.contains(&name)
                    || name == "impl"
                    || name == "dyn"
                    || (name == "Self" && self_kind != Kind::Concrete)
            }
            TokenTree::Group(group) => mentions(&group.stream(), type_params, self_kind),
            TokenTree::Punct(_) | TokenTree::Literal(_) => false,
        })
    }
    if mentions(tokens, type_params, self_kind) {
        Kind::Contains
    } else {
        Kind::Concrete
    }
}

fn mentions_name(tokens: &TokenStream, name: &str) -> bool {
    tokens.clone().into_iter().any(|tree| match tree {
        TokenTree::Ident(ident) => syn::ext::IdentExt::unraw(&ident) == name,
        TokenTree::Group(group) => mentions_name(&group.stream(), name),
        TokenTree::Punct(_) | TokenTree::Literal(_) => false,
    })
}

/// The names of the generic type parameters `generics` declares.
pub(super) fn type_param_names(generics: &syn::Generics) -> BTreeSet<String> {
    generics
        .type_params()
        .map(|param| unraw(&param.ident))
        .collect()
}

fn unraw(ident: &syn::Ident) -> String {
    syn::ext::IdentExt::unraw(ident).to_string()
}

/// One place a body binds names.
struct BindingSite<'a> {
    names: Vec<String>,
    /// The pattern takes the value apart, so a name binds a part of it.
    destructured: bool,
    source: BindingSource<'a>,
}

enum BindingSource<'a> {
    /// `let p = init;`: the names take the kind of `init`.
    Init(&'a Expr),
    /// `let p: ty = ..;` or a typed closure parameter.
    Type(&'a Type),
    /// A `for`, `if let`, `while let` or `match` pattern: the names bind
    /// parts of what the scrutinee yields.
    Scrutinee(&'a Expr),
    /// An untyped closure parameter.
    Unknown,
}

#[derive(Default)]
struct BindingSites<'a> {
    sites: Vec<BindingSite<'a>>,
}

impl<'a> BindingSites<'a> {
    fn push(&mut self, pat: &'a syn::Pat, source: BindingSource<'a>) {
        let (pat, source) = match pat {
            syn::Pat::Type(typed) => (&*typed.pat, BindingSource::Type(&typed.ty)),
            other => (other, source),
        };
        let mut names = PatNames::default();
        names.visit_pat(pat);
        if names.names.is_empty() {
            return;
        }
        self.sites.push(BindingSite {
            names: names.names,
            destructured: !matches!(pat, syn::Pat::Ident(_)),
            source,
        });
    }
}

impl<'a> Visit<'a> for BindingSites<'a> {
    fn visit_item(&mut self, _item: &'a syn::Item) {}

    fn visit_local(&mut self, local: &'a syn::Local) {
        match &local.init {
            Some(init) => self.push(&local.pat, BindingSource::Init(&init.expr)),
            None => self.push(&local.pat, BindingSource::Unknown),
        }
        syn::visit::visit_local(self, local);
    }

    fn visit_expr_for_loop(&mut self, expr: &'a syn::ExprForLoop) {
        self.push(&expr.pat, BindingSource::Scrutinee(&expr.expr));
        syn::visit::visit_expr_for_loop(self, expr);
    }

    fn visit_expr_let(&mut self, expr: &'a syn::ExprLet) {
        self.push(&expr.pat, BindingSource::Scrutinee(&expr.expr));
        syn::visit::visit_expr_let(self, expr);
    }

    fn visit_expr_match(&mut self, expr: &'a syn::ExprMatch) {
        for arm in &expr.arms {
            self.push(&arm.pat, BindingSource::Scrutinee(&expr.expr));
        }
        syn::visit::visit_expr_match(self, expr);
    }

    fn visit_expr_closure(&mut self, expr: &'a syn::ExprClosure) {
        for input in &expr.inputs {
            self.push(input, BindingSource::Unknown);
        }
        syn::visit::visit_expr_closure(self, expr);
    }

    fn visit_expr_assign(&mut self, expr: &'a syn::ExprAssign) {
        self.push_assigned(&expr.left, &expr.right);
        syn::visit::visit_expr_assign(self, expr);
    }

    fn visit_expr_binary(&mut self, expr: &'a syn::ExprBinary) {
        if is_compound_assignment(&expr.op) {
            self.push_assigned(&expr.left, &expr.right);
        }
        syn::visit::visit_expr_binary(self, expr);
    }
}

impl<'a> BindingSites<'a> {
    /// `name = value;` or `name op= value;` rebinds `name` to something of
    /// the kind of `value`.
    fn push_assigned(&mut self, place: &'a Expr, value: &'a Expr) {
        if let Expr::Path(path) = place {
            if let Some(ident) = path.path.get_ident() {
                self.sites.push(BindingSite {
                    names: vec![unraw(ident)],
                    destructured: false,
                    source: BindingSource::Init(value),
                });
            }
        }
    }
}

fn is_compound_assignment(op: &syn::BinOp) -> bool {
    matches!(
        op,
        syn::BinOp::AddAssign(_)
            | syn::BinOp::SubAssign(_)
            | syn::BinOp::MulAssign(_)
            | syn::BinOp::DivAssign(_)
            | syn::BinOp::RemAssign(_)
            | syn::BinOp::BitXorAssign(_)
            | syn::BinOp::BitAndAssign(_)
            | syn::BinOp::BitOrAssign(_)
            | syn::BinOp::ShlAssign(_)
            | syn::BinOp::ShrAssign(_)
    )
}

/// The names a pattern binds.
#[derive(Default)]
struct PatNames {
    names: Vec<String>,
}

impl<'ast> Visit<'ast> for PatNames {
    fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
        self.names.push(unraw(&pat.ident));
        syn::visit::visit_pat_ident(self, pat);
    }
}
