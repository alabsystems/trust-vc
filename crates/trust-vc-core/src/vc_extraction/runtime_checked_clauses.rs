// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The clauses of an exec function that the `trust_vc` macros evaluate at
//! run time, read from the syntax the way the macros read them, and which of
//! them compare values whose comparison the lane may misread.
//!
//! The lane reads every contract clause and spec assertion as ghost code,
//! where a comparison of values of a generic type, or of a type it cannot
//! see, is structural: `x == x` holds for every `x`. Outside a verification
//! build the macros check a clause with `assert!` when it calls nothing (see
//! [`crate::runtime_check`]), and there a comparison runs the operands' own
//! `PartialEq` or `PartialOrd` impl. The lane reads that impl for the
//! primitives, strings, the std containers of those and a type of the file
//! that derives it or whose impl the file shows, and for no other type: a
//! generic type's impl is the caller's choice (`f64::NAN != f64::NAN`), and
//! the impl of a type another file declares is not read. These are the
//! clauses the macros check:
//!
//! * each `requires` and `ensures` clause of `#[trust_vc::contract(..)]`,
//!   with the name its `returns(..)` clause binds read as `result`;
//! * `result == (e)` for `#[trust_vc::returns(e)]`, and for
//!   `#[trust_vc::returns(x)]` on a function that returns a reference;
//! * the condition of `trust_vc::assert!`, `assert_seqs_equal!`,
//!   `invariant!`, `invariant_except_break!`, `requires!` and `ensures!`, and
//!   the measure of `loop_decreases!`.
//!
//! `old!(x)` in a postcondition is the value of `x` on entry, so it is read
//! as `x`. A clause the macros cannot parse does not compile and is not
//! returned. The `#[trust_vc::requires(..)]` and `#[trust_vc::ensures(..)]`
//! attribute spellings are not macros of the crate, so a program that uses
//! them does not compile against it and has no run-time check.

use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::parse::{Parse, ParseStream, Parser};
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::visit_mut::VisitMut;
use syn::{Expr, File, Token};

use super::generic_values::{is_comparison, GenericScope, Kind};
use crate::runtime_check::{runtime_check_evaluates_as_read, ClauseArithmetic};

/// A clause the macros check at run time.
pub(super) struct CheckedClause {
    /// The clause as the lane checks it (see [`checked`]).
    pub(super) expr: Expr,
    /// The clause as written.
    pub(super) source: String,
    /// A precondition, whose check fails when a caller breaks it.
    pub(super) precondition: bool,
}

/// The clauses of `attr` the macros check at run time. `returns_reference`
/// tells whether the function returns a reference.
pub(super) fn checked_attribute_clauses(
    attr: &syn::Attribute,
    returns_reference: bool,
) -> Vec<CheckedClause> {
    let syn::Meta::List(list) = &attr.meta else {
        return Vec::new();
    };
    let Some(name) = attr
        .path()
        .segments
        .last()
        .map(|segment| unraw(&segment.ident))
    else {
        return Vec::new();
    };
    match name.as_str() {
        "contract" => contract_clauses(&list.tokens),
        "returns" => returns_clause(&list.tokens, returns_reference)
            .into_iter()
            .collect(),
        _ => Vec::new(),
    }
}

/// The condition of the spec macro `mac` that the macros check at run time.
/// `mac` is a spec macro (see `bodiless_call_repeat::is_spec_macro`), so an
/// `assert!` here is `trust_vc::assert!` and not std's.
pub(super) fn checked_macro_clause(mac: &syn::Macro) -> Option<CheckedClause> {
    let name = mac
        .path
        .segments
        .last()
        .map(|segment| unraw(&segment.ident))?;
    let tokens = mac.tokens.clone();
    let source = format!("{}!({})", mac.path.to_token_stream(), mac.tokens);
    let (expr, precondition) = match name.as_str() {
        "assert" | "invariant" | "invariant_except_break" => (
            checked(tokens, ClauseArithmetic::FixedWidthChecked, false, None)?,
            false,
        ),
        "ensures" => (
            checked(tokens, ClauseArithmetic::FixedWidthChecked, true, None)?,
            false,
        ),
        "requires" => (
            checked(tokens, ClauseArithmetic::Integer, false, None)?,
            true,
        ),
        "loop_decreases" => {
            let expr = syn::parse2::<Expr>(tokens).ok()?;
            (
                runtime_check_evaluates_as_read(&expr, ClauseArithmetic::Integer)
                    .then_some(expr)?,
                false,
            )
        }
        "assert_seqs_equal" => {
            let input = crate::parse_assert_seqs_equal(tokens).ok()?;
            let (lhs, rhs) = (&input.lhs, &input.rhs);
            let expr: Expr = syn::parse_quote!(#lhs == #rhs);
            (
                runtime_check_evaluates_as_read(&expr, ClauseArithmetic::FixedWidthChecked)
                    .then_some(expr)?,
                false,
            )
        }
        _ => return None,
    };
    Some(CheckedClause {
        expr,
        source,
        precondition,
    })
}

/// True when `clause` compares values whose comparison the lane may read
/// otherwise than the check runs it. `scope` reads the
/// [`opaque_type_names`] as generic type parameters, so an operand of such a
/// type, or holding one, is not concrete there; so is one that names an
/// `opaque_values` item. A name the clause binds itself (in a `let` or a
/// `match` arm) is taken to be of such a type whenever the clause names
/// anything that is.
pub(super) fn compares_opaque_values(
    scope: &GenericScope<'_>,
    clause: &CheckedClause,
    opaque_values: &BTreeSet<String>,
) -> bool {
    let mut locals = LocalNames::default();
    locals.visit_expr(&clause.expr);
    let tokens = clause.expr.to_token_stream();
    let mut finder = ComparisonFinder {
        scope,
        opaque_values,
        locals: locals.names,
        opaque_clause: scope.tokens_mention(&tokens) || names_any(&tokens, opaque_values),
        found: false,
    };
    finder.visit_expr(&clause.expr);
    finder.found
}

/// Names of the types whose comparison the check runs the way the lane reads
/// it when their type arguments' does, and of the modules that lead to them:
/// the primitives (a float compares by IEEE 754 in both), `int` and `nat`
/// (`i128` and `u128` at run time), strings, `PhantomData` and the std
/// containers. The ghost types (`Seq`, `Set`, `Map`, `Multiset`, `Ghost`,
/// `Tracked`, `real`) are listed too: their run-time values are markers, or
/// they do not exist outside a verification build, so what running code does
/// with them is not a question of how a comparison is read.
const STRUCTURAL_TYPE_NAMES: &[&str] = &[
    "u8",
    "u16",
    "u32",
    "u64",
    "u128",
    "usize",
    "i8",
    "i16",
    "i32",
    "i64",
    "i128",
    "isize",
    "f32",
    "f64",
    "bool",
    "char",
    "str",
    "int",
    "nat",
    "String",
    "Vec",
    "VecDeque",
    "Option",
    "Result",
    "Box",
    "Rc",
    "Arc",
    "BTreeMap",
    "BTreeSet",
    "HashMap",
    "HashSet",
    "PhantomData",
    "Seq",
    "Set",
    "Map",
    "Multiset",
    "Ghost",
    "Tracked",
    "real",
    "std",
    "core",
    "alloc",
    "collections",
    "vec",
    "string",
    "option",
    "result",
    "boxed",
    "rc",
    "sync",
    "marker",
    "primitive",
    "crate",
    "self",
    "super",
];

/// The type names of `file` whose comparison the lane may read otherwise
/// than the check runs it; the clause check reads them as generic type
/// parameters. They are the names the file declares as a type or spells as
/// the last segment of a type path, except those of
/// [`STRUCTURAL_TYPE_NAMES`] and the file's own types whose fields, aliased
/// type or associated type definitions name only structural types. A type
/// of the file that does not derive `PartialEq` compares with an impl the
/// lowering reads (or refuses) when the file shows it, and with none
/// otherwise, unless the file declares an out-of-line `mod`, which can
/// implement it; so there it is opaque, and so is an associated type the
/// file defines. A type another file or crate declares and a union are
/// opaque.
pub(super) fn opaque_type_names(file: Option<&File>) -> BTreeSet<String> {
    let Some(file) = file else {
        return BTreeSet::new();
    };
    let mut names = TypeNameCollector::default();
    names.visit_file(file);
    let mut decls = TypeDeclCollector::default();
    decls.visit_file(file);
    let mut imports = ImportCollector::default();
    imports.visit_file(file);
    // A name of the list means the std or ghost type only where the file
    // neither declares it nor imports it from elsewhere, and, under a glob
    // import from elsewhere, only for a primitive.
    let mut structural: BTreeSet<String> = STRUCTURAL_TYPE_NAMES
        .iter()
        .filter(|name| {
            !decls.types.contains_key(**name)
                && !imports.foreign.contains(**name)
                && (!imports.foreign_glob || PRIMITIVE_TYPE_NAMES.contains(name))
        })
        .map(ToString::to_string)
        .chain(decls.modules.iter().cloned())
        .collect();
    loop {
        let before = structural.len();
        for (name, parts) in &decls.types {
            let all_structural = parts.iter().all(|part| {
                !part.union
                    && (part.derived || !decls.out_of_line_mod)
                    && part
                        .idents
                        .iter()
                        .all(|ident| structural.contains(ident) || ident == name)
            });
            if all_structural {
                structural.insert(name.clone());
            }
        }
        if structural.len() == before {
            break;
        }
    }
    names
        .names
        .into_iter()
        .filter(|name| name != "Self" && !structural.contains(name))
        .collect()
}

/// The names of [`STRUCTURAL_TYPE_NAMES`] a glob import cannot stand for,
/// and the roots of paths that lead to the std and ghost types.
const PRIMITIVE_TYPE_NAMES: &[&str] = &[
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize", "f32",
    "f64", "bool", "char", "str", "std", "core", "alloc", "crate", "self", "super",
];

/// Roots of `use` paths whose items are the std and ghost types.
const TRUSTED_USE_ROOTS: &[&str] = &[
    "std",
    "core",
    "alloc",
    "vstd",
    "trust_vc",
    "trust_vc_types",
    "builtin",
    "verus_builtin",
    "self",
    "super",
];

/// The names the file imports with a `use` whose root is not one of
/// [`TRUSTED_USE_ROOTS`], and whether it has a glob import from such a root.
#[derive(Default)]
struct ImportCollector {
    foreign: BTreeSet<String>,
    foreign_glob: bool,
}

impl ImportCollector {
    fn tree(&mut self, tree: &syn::UseTree, root: Option<&str>) {
        let trusted =
            |root: Option<&str>| root.is_some_and(|root| TRUSTED_USE_ROOTS.contains(&root));
        match tree {
            syn::UseTree::Path(path) => {
                let ident = unraw(&path.ident);
                self.tree(&path.tree, Some(root.unwrap_or(&ident)));
            }
            syn::UseTree::Name(name) => {
                let ident = unraw(&name.ident);
                if !trusted(root.or(Some(&ident))) {
                    self.foreign.insert(ident);
                }
            }
            syn::UseTree::Rename(rename) => {
                let ident = unraw(&rename.ident);
                if !trusted(root.or(Some(&ident))) {
                    self.foreign.insert(unraw(&rename.rename));
                }
            }
            syn::UseTree::Glob(_) => {
                if !trusted(root) {
                    self.foreign_glob = true;
                }
            }
            syn::UseTree::Group(group) => {
                for tree in &group.items {
                    self.tree(tree, root);
                }
            }
        }
    }
}

impl<'ast> Visit<'ast> for ImportCollector {
    fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
        self.tree(&item.tree, None);
    }
}

/// The `const`s and `static`s of `file` whose type names an `opaque` type.
pub(super) fn opaque_value_names(
    file: Option<&File>,
    opaque: &BTreeSet<String>,
) -> BTreeSet<String> {
    let mut values = OpaqueValues {
        opaque,
        names: BTreeSet::new(),
    };
    if let Some(file) = file {
        values.visit_file(file);
    }
    values.names
}

/// One clause of `#[trust_vc::contract(..)]`, parsed the way the attribute
/// parses it: a name and a parenthesized list of expressions.
struct ContractClause {
    name: syn::Ident,
    args: Punctuated<Expr, Token![,]>,
}

impl Parse for ContractClause {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let name = input.parse()?;
        let content;
        syn::parenthesized!(content in input);
        let args = Punctuated::parse_terminated(&content)?;
        Ok(ContractClause { name, args })
    }
}

fn contract_clauses(tokens: &TokenStream) -> Vec<CheckedClause> {
    let Ok(clauses) =
        Punctuated::<ContractClause, Token![,]>::parse_terminated.parse2(tokens.clone())
    else {
        return Vec::new();
    };
    let return_name = clauses
        .iter()
        .filter(|clause| clause.name == "returns")
        .find_map(|clause| match clause.args.first() {
            Some(Expr::Path(path)) if clause.args.len() == 1 && path.qself.is_none() => {
                path.path.get_ident().map(unraw)
            }
            _ => None,
        });
    let mut out = Vec::new();
    for clause in &clauses {
        let (arithmetic, precondition) = match unraw(&clause.name).as_str() {
            "requires" => (ClauseArithmetic::Integer, true),
            "ensures" => (ClauseArithmetic::FixedWidthChecked, false),
            _ => continue,
        };
        for arg in &clause.args {
            if let Some(expr) = checked(
                arg.to_token_stream(),
                arithmetic,
                !precondition,
                return_name.as_deref(),
            ) {
                out.push(CheckedClause {
                    expr,
                    source: format!("{}({})", clause.name, arg.to_token_stream()),
                    precondition,
                });
            }
        }
    }
    out
}

fn returns_clause(tokens: &TokenStream, returns_reference: bool) -> Option<CheckedClause> {
    let operand: Expr = if let Ok(ident) = syn::parse2::<syn::Ident>(tokens.clone()) {
        if !returns_reference {
            return None;
        }
        syn::parse_quote!(#ident)
    } else {
        let expr = syn::parse2::<Expr>(tokens.clone()).ok()?;
        let names_only = matches!(
            &expr,
            Expr::Tuple(tuple)
                if !tuple.elems.is_empty()
                    && tuple.elems.iter().all(|elem| matches!(
                        elem,
                        Expr::Path(path) if path.qself.is_none() && path.path.get_ident().is_some()
                    ))
        );
        if names_only {
            return None;
        }
        expr
    };
    let expr: Expr = syn::parse_quote!(result == (#operand));
    runtime_check_evaluates_as_read(&expr, ClauseArithmetic::FixedWidthChecked).then_some(
        CheckedClause {
            expr,
            source: format!("returns({tokens})"),
            precondition: false,
        },
    )
}

/// `tokens` parsed the way the macros parse a clause, with `old!(e)` read as
/// `e` in a postcondition and `return_name` read as `result`, when the
/// macros evaluate it at run time.
fn checked(
    tokens: TokenStream,
    arithmetic: ClauseArithmetic,
    postcondition: bool,
    return_name: Option<&str>,
) -> Option<Expr> {
    let mut expr = crate::parse_expr_tokens_with_chains(tokens).ok()?;
    ClauseRewrite {
        postcondition,
        return_name,
    }
    .visit_expr_mut(&mut expr);
    runtime_check_evaluates_as_read(&expr, arithmetic).then_some(expr)
}

struct ClauseRewrite<'a> {
    postcondition: bool,
    return_name: Option<&'a str>,
}

impl VisitMut for ClauseRewrite<'_> {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        if self.postcondition {
            if let Expr::Macro(mac) = expr {
                let is_old = mac
                    .mac
                    .path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.ident == "old");
                if is_old {
                    if let Ok(inner) = syn::parse2::<Expr>(mac.mac.tokens.clone()) {
                        *expr = syn::parse_quote!((#inner));
                    }
                }
            }
        }
        if let (Some(name), Expr::Path(path)) = (self.return_name, &mut *expr) {
            if path.qself.is_none() && path.path.get_ident().is_some_and(|ident| ident == name) {
                *expr = syn::parse_quote!(result);
                return;
            }
        }
        syn::visit_mut::visit_expr_mut(self, expr);
    }
}

#[derive(Default)]
struct LocalNames {
    names: BTreeSet<String>,
}

impl<'ast> Visit<'ast> for LocalNames {
    fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
        self.names.insert(unraw(&pat.ident));
        syn::visit::visit_pat_ident(self, pat);
    }
}

struct ComparisonFinder<'s, 'd> {
    scope: &'s GenericScope<'d>,
    opaque_values: &'s BTreeSet<String>,
    locals: BTreeSet<String>,
    opaque_clause: bool,
    found: bool,
}

impl ComparisonFinder<'_, '_> {
    fn may_be_opaque(&self, operand: &Expr) -> bool {
        let tokens = operand.to_token_stream();
        self.scope.expr_kind(operand) != Kind::Concrete
            || names_any(&tokens, self.opaque_values)
            || (self.opaque_clause && names_any(&tokens, &self.locals))
    }
}

impl<'ast> Visit<'ast> for ComparisonFinder<'_, '_> {
    fn visit_expr_binary(&mut self, expr: &'ast syn::ExprBinary) {
        if !self.found
            && is_comparison(&expr.op)
            && (self.may_be_opaque(&expr.left) || self.may_be_opaque(&expr.right))
        {
            self.found = true;
        }
        syn::visit::visit_expr_binary(self, expr);
    }
}

/// Every name the file declares as a type or spells as the last segment of
/// a type path, leaving out a generic type parameter where it is in scope.
#[derive(Default)]
struct TypeNameCollector {
    names: BTreeSet<String>,
    /// The generic type parameters of the enclosing items.
    generics: Vec<BTreeSet<String>>,
}

impl TypeNameCollector {
    fn scoped<F: FnOnce(&mut Self)>(&mut self, generics: &syn::Generics, visit: F) {
        self.generics.push(
            generics
                .type_params()
                .map(|param| unraw(&param.ident))
                .collect(),
        );
        visit(self);
        self.generics.pop();
    }

    fn declare(&mut self, ident: &syn::Ident) {
        self.names.insert(unraw(ident));
    }
}

impl<'ast> Visit<'ast> for TypeNameCollector {
    fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
        self.declare(&item.ident);
        self.scoped(&item.generics, |names| {
            syn::visit::visit_item_struct(names, item)
        });
    }

    fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
        self.declare(&item.ident);
        self.scoped(&item.generics, |names| {
            syn::visit::visit_item_enum(names, item)
        });
    }

    fn visit_item_union(&mut self, item: &'ast syn::ItemUnion) {
        self.declare(&item.ident);
        self.scoped(&item.generics, |names| {
            syn::visit::visit_item_union(names, item)
        });
    }

    fn visit_item_type(&mut self, item: &'ast syn::ItemType) {
        self.declare(&item.ident);
        self.scoped(&item.generics, |names| {
            syn::visit::visit_item_type(names, item)
        });
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        self.scoped(&item.sig.generics, |names| {
            syn::visit::visit_item_fn(names, item)
        });
    }

    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        self.scoped(&item.generics, |names| {
            syn::visit::visit_item_impl(names, item)
        });
    }

    fn visit_item_trait(&mut self, item: &'ast syn::ItemTrait) {
        self.scoped(&item.generics, |names| {
            syn::visit::visit_item_trait(names, item)
        });
    }

    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        self.scoped(&item.sig.generics, |names| {
            syn::visit::visit_impl_item_fn(names, item);
        });
    }

    fn visit_trait_item_fn(&mut self, item: &'ast syn::TraitItemFn) {
        self.scoped(&item.sig.generics, |names| {
            syn::visit::visit_trait_item_fn(names, item);
        });
    }

    fn visit_type_path(&mut self, ty: &'ast syn::TypePath) {
        let in_scope_param = ty.qself.is_none()
            && ty.path.get_ident().is_some_and(|ident| {
                let name = unraw(ident);
                self.generics.iter().any(|params| params.contains(&name))
            });
        if !in_scope_param {
            if let Some(last) = ty.path.segments.last() {
                self.names.insert(unraw(&last.ident));
            }
        }
        syn::visit::visit_type_path(self, ty);
    }
}

/// One declaration of a type name of the file.
struct TypeDecl {
    /// It derives `PartialEq`; an alias counts as derived, and an associated
    /// type definition does not.
    derived: bool,
    union: bool,
    /// The names in its field types (the aliased type for an alias), without
    /// its own generic parameters.
    idents: BTreeSet<String>,
}

/// The file's inline modules and type declarations.
#[derive(Default)]
struct TypeDeclCollector {
    modules: BTreeSet<String>,
    out_of_line_mod: bool,
    types: BTreeMap<String, Vec<TypeDecl>>,
}

impl TypeDeclCollector {
    fn record(&mut self, name: &syn::Ident, generics: &syn::Generics, decl: TypeDecl) {
        let params = generic_param_names(generics);
        let TypeDecl {
            derived,
            union,
            mut idents,
        } = decl;
        idents.retain(|ident| !params.contains(ident));
        self.types.entry(unraw(name)).or_default().push(TypeDecl {
            derived,
            union,
            idents,
        });
    }
}

impl<'ast> Visit<'ast> for TypeDeclCollector {
    fn visit_item_mod(&mut self, module: &'ast syn::ItemMod) {
        if module.content.is_some() {
            self.modules.insert(unraw(&module.ident));
        } else {
            self.out_of_line_mod = true;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
        let mut idents = BTreeSet::new();
        for field in &item.fields {
            collect_idents(&field.ty.to_token_stream(), &mut idents);
        }
        let decl = TypeDecl {
            derived: derives_partial_eq(&item.attrs),
            union: false,
            idents,
        };
        self.record(&item.ident, &item.generics, decl);
        syn::visit::visit_item_struct(self, item);
    }

    fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
        let mut idents = BTreeSet::new();
        for field in item
            .variants
            .iter()
            .flat_map(|variant| variant.fields.iter())
        {
            collect_idents(&field.ty.to_token_stream(), &mut idents);
        }
        let decl = TypeDecl {
            derived: derives_partial_eq(&item.attrs),
            union: false,
            idents,
        };
        self.record(&item.ident, &item.generics, decl);
        syn::visit::visit_item_enum(self, item);
    }

    fn visit_item_union(&mut self, item: &'ast syn::ItemUnion) {
        let decl = TypeDecl {
            derived: false,
            union: true,
            idents: BTreeSet::new(),
        };
        self.record(&item.ident, &item.generics, decl);
        syn::visit::visit_item_union(self, item);
    }

    fn visit_item_type(&mut self, item: &'ast syn::ItemType) {
        let mut idents = BTreeSet::new();
        collect_idents(&item.ty.to_token_stream(), &mut idents);
        let decl = TypeDecl {
            derived: true,
            union: false,
            idents,
        };
        self.record(&item.ident, &item.generics, decl);
        syn::visit::visit_item_type(self, item);
    }

    fn visit_impl_item_type(&mut self, item: &'ast syn::ImplItemType) {
        let mut idents = BTreeSet::new();
        collect_idents(&item.ty.to_token_stream(), &mut idents);
        let decl = TypeDecl {
            derived: false,
            union: false,
            idents,
        };
        self.record(&item.ident, &item.generics, decl);
        syn::visit::visit_impl_item_type(self, item);
    }
}

/// True when `attrs` hold `#[derive(..)]` naming `PartialEq`.
fn derives_partial_eq(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path().is_ident("derive")
            && matches!(&attr.meta, syn::Meta::List(list) if {
                let mut idents = BTreeSet::new();
                collect_idents(&list.tokens, &mut idents);
                idents.contains("PartialEq")
            })
    })
}

/// The type, const and lifetime parameters `generics` declares.
fn generic_param_names(generics: &syn::Generics) -> BTreeSet<String> {
    generics
        .params
        .iter()
        .map(|param| match param {
            syn::GenericParam::Type(param) => unraw(&param.ident),
            syn::GenericParam::Const(param) => unraw(&param.ident),
            syn::GenericParam::Lifetime(param) => unraw(&param.lifetime.ident),
        })
        .collect()
}

/// The identifiers in `tokens`, leaving out lifetime names, `mut`, `const`
/// and `Self` (the type being declared).
fn collect_idents(tokens: &TokenStream, out: &mut BTreeSet<String>) {
    let mut after_quote = false;
    for tree in tokens.clone() {
        match tree {
            proc_macro2::TokenTree::Ident(ident) => {
                let name = unraw(&ident);
                if !after_quote && !matches!(name.as_str(), "mut" | "const" | "Self") {
                    out.insert(name);
                }
                after_quote = false;
            }
            proc_macro2::TokenTree::Group(group) => {
                collect_idents(&group.stream(), out);
                after_quote = false;
            }
            proc_macro2::TokenTree::Punct(punct) => after_quote = punct.as_char() == '\'',
            proc_macro2::TokenTree::Literal(_) => after_quote = false,
        }
    }
}

struct OpaqueValues<'s> {
    opaque: &'s BTreeSet<String>,
    names: BTreeSet<String>,
}

impl<'ast> Visit<'ast> for OpaqueValues<'_> {
    fn visit_item_const(&mut self, item: &'ast syn::ItemConst) {
        if names_any(&item.ty.to_token_stream(), self.opaque) {
            self.names.insert(unraw(&item.ident));
        }
        syn::visit::visit_item_const(self, item);
    }

    fn visit_item_static(&mut self, item: &'ast syn::ItemStatic) {
        if names_any(&item.ty.to_token_stream(), self.opaque) {
            self.names.insert(unraw(&item.ident));
        }
        syn::visit::visit_item_static(self, item);
    }

    fn visit_impl_item_const(&mut self, item: &'ast syn::ImplItemConst) {
        if names_any(&item.ty.to_token_stream(), self.opaque) {
            self.names.insert(unraw(&item.ident));
        }
        syn::visit::visit_impl_item_const(self, item);
    }
}

pub(super) fn names_any(tokens: &TokenStream, names: &BTreeSet<String>) -> bool {
    tokens.clone().into_iter().any(|tree| match tree {
        proc_macro2::TokenTree::Ident(ident) => names.contains(&unraw(&ident)),
        proc_macro2::TokenTree::Group(group) => names_any(&group.stream(), names),
        proc_macro2::TokenTree::Punct(_) | proc_macro2::TokenTree::Literal(_) => false,
    })
}

fn unraw(ident: &syn::Ident) -> String {
    syn::ext::IdentExt::unraw(ident).to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn attr_clauses(attr: &str, returns_reference: bool) -> Vec<String> {
        let item: syn::ItemFn =
            syn::parse_str(&format!("{attr} fn f() {{}}")).expect("fixture parses");
        item.attrs
            .iter()
            .flat_map(|attr| checked_attribute_clauses(attr, returns_reference))
            .map(|clause| clause.expr.to_token_stream().to_string())
            .collect()
    }

    fn macro_clause(mac: &str) -> Option<(String, bool)> {
        let mac: syn::Macro = syn::parse_str(mac).expect("fixture parses");
        checked_macro_clause(&mac).map(|clause| {
            (
                clause.expr.to_token_stream().to_string(),
                clause.precondition,
            )
        })
    }

    #[test]
    fn the_clauses_the_macros_check_are_read_as_the_macros_read_them() {
        assert_eq!(
            attr_clauses(
                "#[trust_vc::contract(requires(a == b, n > 0u64), ensures(r == x), returns(r))]",
                false
            ),
            ["a == b", "n > 0u64", "result == x"]
        );
        assert_eq!(
            attr_clauses("#[contract(ensures(r == old!(x)), returns(r))]", false),
            ["result == (x)"]
        );
        assert_eq!(
            attr_clauses("#[trust_vc::returns(x + 1u64)]", false),
            ["result == (x + 1u64)"]
        );
        assert_eq!(
            attr_clauses("#[trust_vc::returns(x)]", true),
            ["result == (x)"]
        );
        assert_eq!(
            macro_clause("trust_vc::assert!(x == y)"),
            Some(("x == y".to_string(), false))
        );
        assert_eq!(
            macro_clause("requires!(a == b)"),
            Some(("a == b".to_string(), true))
        );
        assert_eq!(
            macro_clause("invariant!(i <= n && x == x)"),
            Some(("i <= n && x == x".to_string(), false))
        );
        assert_eq!(
            macro_clause("assert_seqs_equal!(a == b)"),
            Some(("a == b".to_string(), false))
        );
    }

    #[test]
    fn a_clause_the_macros_do_not_evaluate_is_not_checked() {
        for attr in [
            "#[trust_vc::contract(ensures(r == inc(x)), returns(r))]",
            "#[trust_vc::contract(ensures(r == x.view()), returns(r))]",
            "#[trust_vc::contract(requires(x + 1u64 > x), ensures(true), returns(r))]",
            "#[trust_vc::contract(recommends(x == y), ensures(true), returns(r))]",
            "#[trust_vc::returns(r)]",
            "#[trust_vc::returns((a, b))]",
            "#[trust_vc::ensures(result == x)]",
            "#[trust_vc::requires(x == y)]",
        ] {
            let clauses = attr_clauses(attr, false);
            assert!(
                clauses
                    .iter()
                    .all(|clause| !clause.contains("==") || clause == "true"),
                "{attr}: {clauses:?}"
            );
        }
        for mac in [
            "trust_vc::assert!(inc(x) == x)",
            "trust_vc::assert!(forall!(|i: u64| i == i))",
            "assume!(x == y)",
            "proof_block!(x == y)",
            "recommends!(x == y)",
        ] {
            assert_eq!(macro_clause(mac), None, "{mac}");
        }
    }

    fn opaque(src: &str) -> BTreeSet<String> {
        opaque_type_names(Some(&syn::parse_file(src).expect("fixture parses")))
    }

    #[test]
    fn a_type_whose_comparison_the_file_does_not_show_is_opaque() {
        let names = opaque(
            "mod other; use other::S; use std::collections::HashMap;
             #[derive(PartialEq)] struct D { a: u64, v: Vec<u8>, s: String }
             #[derive(PartialEq)] struct Df { f: f64 }
             #[derive(PartialEq)] struct Dn { d: D, o: Option<Box<D>> }
             #[derive(PartialEq)] struct Dg<T> { t: T, n: u64 }
             #[derive(PartialEq)] struct Dl<'a> { s: &'a str }
             #[derive(PartialEq)] struct Ds { s: S }
             struct N { a: u64 }
             struct H { a: u64 }
             impl PartialEq for H { fn eq(&self, o: &H) -> bool { false } }
             #[derive(PartialEq)] struct Ho { a: u64 }
             impl PartialOrd for Ho { fn partial_cmp(&self, o: &Ho) -> Option<core::cmp::Ordering> { None } }
             union U { a: u64 }
             type A = D;
             type As = Ds;
             mod inner { #[derive(PartialEq)] pub struct I { pub a: u64 } }
             fn f(a: inner::I, b: HashMap<u64, u64>, c: Dg<u64>, e: A, h: Seq<u64>, i: nat) {}",
        );
        for name in ["S", "Ds", "N", "H", "U", "As"] {
            assert!(names.contains(name), "{name} should be opaque: {names:?}");
        }
        for name in [
            "D", "Df", "Dn", "Dg", "Dl", "A", "I", "Ho", "HashMap", "u64", "u8", "f64", "nat",
            "String", "Vec", "Option", "Box", "str", "Seq", "other", "inner", "Self", "T",
        ] {
            assert!(
                !names.contains(name),
                "{name} should compare structurally: {names:?}"
            );
        }
        // A list name the file declares, or imports from elsewhere, is its
        // own; under a glob from elsewhere, only a primitive is known.
        let names = opaque(
            "use other::Set; struct Seq { f: other::S } fn f(a: Set<u64>, b: Seq, c: Map<u64, u64>) {}",
        );
        for name in ["Set", "Seq"] {
            assert!(names.contains(name), "{name} should be opaque: {names:?}");
        }
        assert!(!names.contains("Map"), "{names:?}");
        let names = opaque("use other::*; fn f(a: Vec<u64>, b: u64) {}");
        assert!(names.contains("Vec"), "{names:?}");
        assert!(!names.contains("u64"), "{names:?}");
        let names = opaque("use vstd::prelude::*; use std::collections::HashMap; fn f(a: Seq<u64>, b: HashMap<u8, u8>) {}");
        assert!(
            !names.contains("Seq") && !names.contains("HashMap"),
            "{names:?}"
        );
        // Without an out-of-line `mod`, a type of the file with no derive has
        // no impl this file does not show, and an associated type is what the
        // file's impls define it as.
        let names = opaque(
            "struct N { a: u64 } trait Tr { type X; type Y; } struct Z;
             impl Tr for Z { type X = u8; type Y = other::S; }
             fn f(n: N, x: <Z as Tr>::X, y: <Z as Tr>::Y) {}",
        );
        for name in ["N", "X"] {
            assert!(
                !names.contains(name),
                "{name} should compare structurally: {names:?}"
            );
        }
        for name in ["Y", "S"] {
            assert!(names.contains(name), "{name} should be opaque: {names:?}");
        }
    }
}
