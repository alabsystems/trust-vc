//! H10 — generic instantiation carriage for source-function helper symbols.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! A call to a source function lowers to `name(args)`: the turbofish is never
//! part of the solver term. Two instantiations the ARGUMENTS do not already
//! separate therefore collapse into one uninterpreted symbol, and the engine
//! used to prove `tid::<usize>() == tid::<u64>()`, transfer a fact pinned about
//! `tid::<u8>()` to `tid::<u64>()`, and verify an exec sibling
//! `ereq::<u8>() == ereq::<u64>()` whose runtime values are 1 and 8.
//!
//! THE RULE. A generic declaration may become a helper symbol only if
//!
//! 1. no generic parameter name is SHADOWED — the lowering environment has no
//!    notion of generic scope, so a parameter spelled like a type it can
//!    resolve (`type T = u8;` at file level, a source struct, a builtin such as
//!    `u8`) is silently read as that type inside the signature and the body,
//!    and `fn tsz<T>() -> usize { size_of::<T>() }` published `tsz() == 1` for
//!    every instantiation; and
//! 2. every generic parameter is CARRIED into the term (see
//!    [`uncarried_generic_params`]) — or the definition's axiom is published
//!    unconditionally. A published body is lowered in the erased environment,
//!    where every instantiation-dependent construct fails to lower
//!    (`size_of::<T>()`, `T::N`, a nested uncarried call) and a lowering failure
//!    fails the whole query; with rule 1 in force, a body that DOES lower
//!    denotes the same value at every instantiation, so identifying the
//!    instantiations is exactly Rust's semantics. Const generics are never
//!    exempt: their VALUE is the instantiation.
//!
//! Anything else fails closed. The call-site half (a carrying argument must be
//! the instantiation the turbofish names) lives in
//! `ir_lowering::dispatch::calls`.
// quality-audit: allow-file allow-rust-size — the generic-instantiation carriage rules and their refusals, kept together

use std::collections::BTreeSet;

use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::TrustVcType;
use crate::vc::VerificationContext;

/// Type- and value-namespace names a source file declares, which the lowering
/// environment may resolve a bare generic-parameter spelling to.
///
/// Collected at every module depth: the lowering maps are keyed by bare name,
/// so a module-local `type T = u8;` is as dangerous as a root one. Glob imports
/// are not enumerable and are ignored — the environment only resolves names the
/// FILE declares (plus builtins, checked separately), never a glob's exports.
#[derive(Clone, Debug, Default)]
pub(crate) struct GenericShadowNames {
    /// Struct names: resolved through the struct registry, which the source
    /// catalog's signature resolution already guards with the signature's own
    /// generics (`spec_fn_generic_shadowed_by_struct.rs`).
    structs: BTreeSet<String>,
    /// Every other type-namespace name (enums and type aliases — both land in
    /// the context's flat alias map — unions, traits, imported names).
    types: BTreeSet<String>,
    values: BTreeSet<String>,
}

impl GenericShadowNames {
    pub(crate) fn from_file(file: &syn::File) -> Self {
        let mut names = Self::default();
        names.collect_items(&file.items);
        names
    }

    fn collect_items(&mut self, items: &[syn::Item]) {
        for item in items {
            match item {
                syn::Item::Struct(item) => {
                    self.structs.insert(item.ident.to_string());
                    self.values.insert(item.ident.to_string());
                }
                syn::Item::Enum(item) => {
                    self.types.insert(item.ident.to_string());
                }
                syn::Item::Union(item) => {
                    self.types.insert(item.ident.to_string());
                }
                syn::Item::Type(item) => {
                    self.types.insert(item.ident.to_string());
                }
                syn::Item::Trait(item) => {
                    self.types.insert(item.ident.to_string());
                }
                syn::Item::TraitAlias(item) => {
                    self.types.insert(item.ident.to_string());
                }
                syn::Item::Const(item) => {
                    self.values.insert(item.ident.to_string());
                }
                syn::Item::Static(item) => {
                    self.values.insert(item.ident.to_string());
                }
                syn::Item::Use(item) => self.collect_use_tree(&item.tree),
                syn::Item::Mod(item) => {
                    if let Some((_, items)) = &item.content {
                        self.collect_items(items);
                    }
                }
                _ => {}
            }
        }
    }

    fn collect_use_tree(&mut self, tree: &syn::UseTree) {
        match tree {
            syn::UseTree::Path(path) => self.collect_use_tree(&path.tree),
            syn::UseTree::Name(name) => {
                self.types.insert(name.ident.to_string());
                self.values.insert(name.ident.to_string());
            }
            syn::UseTree::Rename(rename) => {
                self.types.insert(rename.rename.to_string());
                self.values.insert(rename.rename.to_string());
            }
            syn::UseTree::Group(group) => {
                for tree in &group.items {
                    self.collect_use_tree(tree);
                }
            }
            syn::UseTree::Glob(_) => {}
        }
    }
}

/// Generic parameters of `sig` that the solver term of a call does NOT carry.
///
/// The only per-instantiation carriers the encoder has are the type-keyed
/// `Box_P` it wraps around an argument at a value parameter whose REGISTERED
/// type is exactly `TypeParam(P)`, and the source catalog's per-query datatype
/// monomorphization (`mono_bound`), whose concrete carrier sort differs per
/// instantiation. Everything else was measured to collapse:
///
/// * const generics (`cz::<3>()` and `cz::<4>()`) — listed in
///   [`UncarriedGenerics::consts`];
/// * nested-only occurrences (`PhantomData<P>` erases to `Unit`; `Option<P>`,
///   `Seq<P>` ride on Poly/template sorts);
/// * return-only occurrences (`fn pick<P>() -> Seq<P>`).
///
/// Lifetimes are ignored: they have no runtime meaning.
pub(crate) fn uncarried_generic_params(
    sig: &syn::Signature,
    registered_params: &[TrustVcType],
    mono_bound: &[(String, TrustVcType)],
) -> UncarriedGenerics {
    let mut uncarried = UncarriedGenerics::default();
    for param in &sig.generics.params {
        match param {
            syn::GenericParam::Const(const_param) => {
                uncarried.consts.push(const_param.ident.to_string());
            }
            syn::GenericParam::Type(type_param) => {
                let name = type_param.ident.to_string();
                let carried = registered_params
                    .iter()
                    .any(|ty| matches!(ty, TrustVcType::TypeParam(param) if *param == name))
                    || mono_bound.iter().any(|(param, _)| *param == name);
                if !carried {
                    uncarried.types.push(name);
                }
            }
            syn::GenericParam::Lifetime(_) => {}
        }
    }
    uncarried
}

/// The declaration-order names of `sig`'s type and const generic parameters —
/// exactly the parameters a turbofish instantiates, in turbofish order
/// (lifetimes are skipped: a turbofish's lifetime arguments precede and never
/// interleave with them).
pub(crate) fn declaration_generic_params(sig: &syn::Signature) -> Vec<String> {
    sig.generics
        .params
        .iter()
        .filter_map(|param| match param {
            syn::GenericParam::Type(type_param) => Some(type_param.ident.to_string()),
            syn::GenericParam::Const(const_param) => Some(const_param.ident.to_string()),
            syn::GenericParam::Lifetime(_) => None,
        })
        .collect()
}

/// The generic parameters of a declaration that no call term carries.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct UncarriedGenerics {
    /// Type parameters no value parameter carries.
    pub(crate) types: Vec<String>,
    /// Const parameters — never carried, and never exempt.
    pub(crate) consts: Vec<String>,
}

impl UncarriedGenerics {
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.types.is_empty() && self.consts.is_empty()
    }
}

/// Generic parameters of a declaration whose bare spelling the lowering
/// environment resolves to something other than an erased type parameter, at a
/// place the declaration actually spells it.
///
/// A type parameter collides with a type the file declares at any depth (or
/// imports by name), a source type alias or struct already in `ctx`, or a builtin
/// the type parser reads as a concrete type (`u8`, `int`, `String`, ...). A
/// collision is a misread only where the name is SPELLED: anywhere in `block`
/// (the body is lowered with no generic scope at all), or in the signature's
/// parameter and return types — except that a struct collision in the signature
/// is excused when `signature_guards_structs` (the source catalog resolves
/// signature types with the signature's own generics shadowing the struct
/// registry) AND the name parses as a short-uppercase type parameter, the only
/// spelling that guard covers. A const parameter collides with a value or type
/// the file declares or imports.
pub(crate) fn shadowed_generic_params(
    sig: &syn::Signature,
    block: &syn::Block,
    names: &GenericShadowNames,
    ctx: &VerificationContext,
    signature_guards_structs: bool,
) -> Vec<String> {
    if sig.generics.params.is_empty() {
        return Vec::new();
    }
    let mut body_idents = BTreeSet::new();
    collect_idents(quote::quote!(#block), &mut body_idents);
    let mut signature_idents = BTreeSet::new();
    for input in &sig.inputs {
        collect_idents(quote::quote!(#input), &mut signature_idents);
    }
    let output = &sig.output;
    collect_idents(quote::quote!(#output), &mut signature_idents);

    sig.generics
        .params
        .iter()
        .filter_map(|param| match param {
            syn::GenericParam::Type(type_param) => {
                let name = type_param.ident.to_string();
                let in_body = body_idents.contains(&name);
                let in_signature = signature_idents.contains(&name);
                let parsed = TrustVcType::parse_or_opaque(&name);
                let builtin = !matches!(
                    parsed,
                    TrustVcType::TypeParam(ref parsed) | TrustVcType::Opaque(ref parsed)
                        if *parsed == name
                );
                // The catalog's signature guard lives only on the parser's
                // short-uppercase `TypeParam` arm; a longer name (`Key`) parses
                // `Opaque` and resolves to a same-named struct unguarded.
                let signature_guards_structs = signature_guards_structs
                    && matches!(parsed, TrustVcType::TypeParam(ref parsed) if *parsed == name);
                let alias_like = builtin
                    || names.types.contains(&name)
                    || ctx.source_type_aliases().contains_key(&name);
                let struct_like = names.structs.contains(&name)
                    || ctx
                        .struct_types
                        .iter()
                        .any(|struct_def| struct_def.name == name);
                let shadowed = (alias_like && (in_body || in_signature))
                    || (struct_like && (in_body || (in_signature && !signature_guards_structs)));
                shadowed.then_some(name)
            }
            syn::GenericParam::Const(const_param) => {
                let name = const_param.ident.to_string();
                let collides = names.values.contains(&name)
                    || names.types.contains(&name)
                    || names.structs.contains(&name);
                (collides && (body_idents.contains(&name) || signature_idents.contains(&name)))
                    .then_some(name)
            }
            syn::GenericParam::Lifetime(_) => None,
        })
        .collect()
}

fn collect_idents(tokens: proc_macro2::TokenStream, out: &mut BTreeSet<String>) {
    for token in tokens {
        match token {
            proc_macro2::TokenTree::Ident(ident) => {
                out.insert(ident.to_string());
            }
            proc_macro2::TokenTree::Group(group) => collect_idents(group.stream(), out),
            _ => {}
        }
    }
}

/// Every expression an attribute list carries, parsed permissively: a
/// comma-separated list (`contract(requires(a), ensures(b))`, `requires(a, b)`)
/// or a single expression. An attribute that parses as neither contributes
/// nothing — the strict contract extraction fails the query on such a clause
/// anyway.
///
/// Used only to find turbofish HINTS (`gop::<u8>(..)`) a contract hides, so an
/// over-approximation (a `derive(..)` list parses as paths) is harmless.
pub(crate) fn attribute_clause_exprs(attrs: &[syn::Attribute]) -> Vec<syn::Expr> {
    use syn::parse::Parser as _;
    let mut exprs = Vec::new();
    for attr in attrs {
        let syn::Meta::List(list) = &attr.meta else {
            continue;
        };
        let parsed = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
            .parse2(list.tokens.clone());
        match parsed {
            Ok(list) => exprs.extend(list),
            Err(_) => {
                if let Ok(expr) = syn::parse2::<syn::Expr>(list.tokens.clone()) {
                    exprs.push(expr);
                }
            }
        }
    }
    exprs
}

/// The attribute clause expressions of EVERY fn-like item in `items`, at any
/// module depth: free fns, inherent and trait impl methods, trait methods. A
/// callee's `ensures` is assumed at its call sites, so a turbofish it spells
/// reaches the verified function's query exactly like one in that function's
/// own contracts.
pub(crate) fn contract_clause_exprs_in_items(items: &[syn::Item]) -> Vec<syn::Expr> {
    let mut exprs = Vec::new();
    for item in items {
        match item {
            syn::Item::Fn(item_fn) => exprs.extend(attribute_clause_exprs(&item_fn.attrs)),
            syn::Item::Impl(item_impl) => {
                for impl_item in &item_impl.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        exprs.extend(attribute_clause_exprs(&method.attrs));
                    }
                }
            }
            syn::Item::Trait(item_trait) => {
                for trait_item in &item_trait.items {
                    if let syn::TraitItem::Fn(method) = trait_item {
                        exprs.extend(attribute_clause_exprs(&method.attrs));
                    }
                }
            }
            syn::Item::Mod(item_mod) => {
                if let Some((_, items)) = &item_mod.content {
                    exprs.extend(contract_clause_exprs_in_items(items));
                }
            }
            _ => {}
        }
    }
    exprs
}

/// Enforce THE RULE for one helper registration of the generic source
/// declaration `name`.
///
/// `definition_is_unconditional` is true only when the registration publishes
/// the definitional body axiom for every use (a transparent spec body that is
/// not opaque, not uninterpreted and not recursion-suppressed; an exec sibling
/// whose body axiom is published).
pub(crate) fn check_generic_declaration(
    context: &'static str,
    name: &str,
    shadowed: &[String],
    uncarried: &UncarriedGenerics,
    definition_is_unconditional: bool,
) -> TrustVcResult<()> {
    if !shadowed.is_empty() {
        return Err(TrustVcError::Encoding {
            context,
            detail: format!(
                "generic parameter shadowed: source function `{name}` declares generic \
                 parameter(s) {} spelled like a type or value the lowering environment \
                 resolves; its signature and body would be read at that item instead of the \
                 instantiation, so TrustVc fails closed",
                backticked(shadowed)
            ),
        });
    }
    if !uncarried.consts.is_empty() {
        return Err(not_carried(
            context,
            name,
            &uncarried.consts,
            "const generic parameter(s)",
            "a const generic's value is the instantiation itself",
        ));
    }
    if !uncarried.types.is_empty() && !definition_is_unconditional {
        return Err(not_carried(
            context,
            name,
            &uncarried.types,
            "generic parameter(s)",
            "no unconditionally published definition makes its value independent of the \
             instantiation",
        ));
    }
    Ok(())
}

fn not_carried(
    context: &'static str,
    name: &str,
    params: &[String],
    kind: &str,
    why: &str,
) -> TrustVcError {
    TrustVcError::Encoding {
        context,
        detail: format!(
            "generic instantiation not carried: source function `{name}` declares {kind} {} \
             that no value parameter carries into its solver term, and {why}; calls at \
             different instantiations would collapse into one uninterpreted symbol, so \
             TrustVc fails closed",
            backticked(params)
        ),
    }
}

fn backticked(params: &[String]) -> String {
    params
        .iter()
        .map(|param| format!("`{param}`"))
        .collect::<Vec<_>>()
        .join(", ")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sig(src: &str) -> syn::Signature {
        syn::parse_str::<syn::ItemFn>(src).expect("fn parses").sig
    }

    #[test]
    fn carriage_is_exact_type_param_or_mono_binding() {
        let tid = sig("fn tid<T>() -> int { 0 }");
        assert_eq!(uncarried_generic_params(&tid, &[], &[]).types, vec!["T"]);

        let bare = sig("fn bare<T>(x: T) -> int { 0 }");
        let carried = [TrustVcType::TypeParam("T".into())];
        assert!(uncarried_generic_params(&bare, &carried, &[]).is_empty());

        let two = sig("fn two<A, B>(a: A) -> int { 0 }");
        let first_only = [TrustVcType::TypeParam("A".into())];
        assert_eq!(
            uncarried_generic_params(&two, &first_only, &[]).types,
            vec!["B"]
        );

        let glen = sig("fn glen<T>(l: GList<T>) -> int { 0 }");
        let mono = [("T".to_string(), TrustVcType::Int { width: 32 })];
        assert!(uncarried_generic_params(&glen, &[], &mono).is_empty());

        let cz = sig("fn cz<'a, const N: usize>() -> int { 0 }");
        let uncarried = uncarried_generic_params(&cz, &[], &[]);
        assert!(uncarried.types.is_empty());
        assert_eq!(uncarried.consts, vec!["N"]);
    }

    #[test]
    fn shadowing_covers_file_items_builtins_and_imports() {
        let file = syn::parse_file(
            "type T = u8;
             struct U { a: u8 }
             const N: usize = 3;
             mod m { pub type V = u16; }
             use std::collections::HashMap as W;",
        )
        .expect("file parses");
        let names = GenericShadowNames::from_file(&file);
        let ctx = VerificationContext::new();
        let shadowed_with = |src: &str, guards: bool| {
            let item = syn::parse_str::<syn::ItemFn>(src).expect("fn parses");
            shadowed_generic_params(&item.sig, &item.block, &names, &ctx, guards)
        };
        let shadowed = |src: &str| shadowed_with(src, false);

        let size = "core::mem::size_of::<X>()";
        assert_eq!(
            shadowed(&format!(
                "fn a<T>() -> usize {{ {} }}",
                size.replace('X', "T")
            )),
            vec!["T"]
        );
        assert_eq!(shadowed("fn a<T>(x: T) -> int { 0 }"), vec!["T"]);
        assert_eq!(shadowed("fn a<V>() -> usize { size_of::<V>() }"), vec!["V"]);
        assert_eq!(shadowed("fn a<W>(w: W) -> int { 0 }"), vec!["W"]);
        assert_eq!(shadowed("fn a<u8>() -> u8 { 0 }"), vec!["u8"]);
        assert_eq!(shadowed("fn a<const N: usize>() -> usize { N }"), vec!["N"]);
        assert!(shadowed("fn a<A, Key, const M: usize>() -> usize { M }").is_empty());
        // A collision the declaration never spells is no misread.
        assert!(shadowed("fn a<T>() -> int { 0 }").is_empty());
        // A struct collision in the signature is excused only where signature
        // resolution guards it; in the body it never is.
        assert_eq!(
            shadowed_with("fn a<U>(x: U) -> bool { true }", false),
            vec!["U"]
        );
        assert!(shadowed_with("fn a<U>(x: U) -> bool { true }", true).is_empty());
        // ...and only for a short-uppercase name: `Key` parses `Opaque`, which
        // the catalog resolves to a same-named struct without the guard.
        let key_file = syn::parse_file("struct Key { a: u8 }").expect("file parses");
        let key_names = GenericShadowNames::from_file(&key_file);
        let key =
            syn::parse_str::<syn::ItemFn>("fn a<Key>(k: Key) -> bool { true }").expect("fn parses");
        assert_eq!(
            shadowed_generic_params(&key.sig, &key.block, &key_names, &ctx, true),
            vec!["Key"]
        );
        assert_eq!(
            shadowed_with("fn a<U>(x: U) -> usize { size_of::<U>() }", true),
            vec!["U"]
        );
    }

    #[test]
    fn attribute_clauses_are_collected_from_every_spelling_and_depth() {
        let file = syn::parse_file(
            "#[trust_vc::contract(requires(gop::<u8>(GList::GNil) == 1), ensures(true))]
             fn a() {}
             #[trust_vc::requires(x > 0, y > 0)]
             fn b(x: u64, y: u64) {}
             impl S {
                 #[trust_vc::ensures(m::<u16>() == 2)]
                 fn c(&self) {}
             }
             trait T {
                 #[trust_vc::ensures(result)]
                 fn d(&self) -> bool { true }
             }
             mod inner {
                 #[trust_vc::ensures(deep::<u32>() == 3)]
                 fn e() {}
             }",
        )
        .expect("file parses");
        let exprs = contract_clause_exprs_in_items(&file.items);
        let rendered = exprs
            .iter()
            .map(|expr| quote::quote!(#expr).to_string())
            .collect::<Vec<_>>();
        // Multi-clause `contract(..)` yields both clauses, and a multi-argument
        // `requires(a, b)` (whose attribute tokens are `a, b`) yields each.
        assert_eq!(rendered.len(), 7, "{rendered:?}");
        assert!(rendered[0].contains("gop :: < u8 >"), "{rendered:?}");
        assert!(rendered[1].starts_with("ensures"), "{rendered:?}");
        assert_eq!(rendered[2], "x > 0", "{rendered:?}");
        assert_eq!(rendered[3], "y > 0", "{rendered:?}");
        assert!(rendered[4].contains("m :: < u16 >"), "{rendered:?}");
        assert_eq!(rendered[5], "result", "{rendered:?}");
        assert!(rendered[6].contains("deep :: < u32 >"), "{rendered:?}");
    }

    #[test]
    fn refusal_order_and_exemption() {
        let none = UncarriedGenerics::default();
        assert!(check_generic_declaration("t", "f", &[], &none, false).is_ok());

        let types = UncarriedGenerics {
            types: vec!["T".into()],
            consts: vec![],
        };
        assert!(check_generic_declaration("t", "f", &[], &types, true).is_ok());
        let err = check_generic_declaration("t", "f", &[], &types, false)
            .expect_err("uncarried and conditional is refused")
            .to_string();
        assert!(err.contains("generic instantiation not carried") && err.contains("`f`"));

        let consts = UncarriedGenerics {
            types: vec![],
            consts: vec!["N".into()],
        };
        assert!(check_generic_declaration("t", "f", &[], &consts, true).is_err());

        let err = check_generic_declaration("t", "f", &["T".into()], &none, true)
            .expect_err("shadowing is refused even when exempt")
            .to_string();
        assert!(err.contains("generic parameter shadowed"));
    }
}
