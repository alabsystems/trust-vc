//! Well-formedness (upstream order) and D1a admission for `state_machine!`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The checks run in the order the pinned upstream macro runs them
//! (`parse_token_stream.rs` `parse_result_to_smir`, `transitions.rs`
//! `check_transitions`, `lemmas.rs` `check_lemmas`), with upstream's own
//! message text, so a ported upstream error case reports the upstream
//! fragment. Only after every upstream check passes does the D1a admission
//! pass run: it admits exactly the surface the relation compiler models
//! completely and refuses everything else by name.

use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, Expr, Ident, Item, Meta, Pat, Type};

use super::parse::{
    parse_transition, LetKind, MachineAst, Refute, SpecialOp, SubIdx, TStmt, TransitionAst,
    TransitionKind, TransitionParam,
};
use super::GENERATED_PREFIX;

/// A field of an admitted machine.
#[derive(Clone)]
pub(crate) struct FieldDef {
    pub(crate) name: Ident,
    pub(crate) ty: Type,
}

#[derive(Clone)]
pub(crate) struct InvariantDef {
    pub(crate) func: syn::ItemFn,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum LemmaKind {
    Init,
    Transition,
}

impl LemmaKind {
    pub(crate) fn label(self) -> &'static str {
        match self {
            LemmaKind::Init => "init",
            LemmaKind::Transition => "transition",
        }
    }
}

#[derive(Clone)]
pub(crate) struct LemmaDef {
    pub(crate) func: syn::ItemFn,
    pub(crate) target: Ident,
    pub(crate) kind: LemmaKind,
}

/// A machine that passed upstream well-formedness AND D1a admission.
#[derive(Clone)]
pub(crate) struct Machine {
    pub(crate) name: Ident,
    pub(crate) fields: Vec<FieldDef>,
    pub(crate) transitions: Vec<TransitionAst>,
    pub(crate) invariants: Vec<InvariantDef>,
    pub(crate) lemmas: Vec<LemmaDef>,
}

type FileDeclaration = (Vec<String>, Option<Item>);

/// Per-file facts D1a admission reads. `None` on the proc-macro lane, which
/// has no file; there the rustc type checker, not this pass, decides datatype
/// paths, and no verification claim is made.
pub(crate) struct FileFacts {
    /// Bare name -> declarations (module path, item) of structs/enums/unions/
    /// type aliases/traits, plus `use`-bound names (item `None`).
    decls: BTreeMap<String, Vec<FileDeclaration>>,
    /// Bare self-type names with a hand-written `PartialEq`/`Eq` impl.
    manual_eq: BTreeSet<String>,
    /// Every item ident anywhere in the file (fns, methods, types, mods,
    /// consts, statics, traits, macro_rules, use bindings) with counts.
    item_names: BTreeMap<String, usize>,
    /// Every fn / method ident anywhere, with counts.
    fn_names: BTreeMap<String, usize>,
    /// File-root `#[trust_vc::spec]` free fns.
    root_spec_fns: BTreeMap<String, syn::ItemFn>,
    /// Names DECLARED by an item (not bound by a `use`).
    declared_items: BTreeSet<String>,
}

impl FileFacts {
    /// Facts of `items` EXCLUDING the item-macro invocations themselves.
    pub(crate) fn collect(items: &[Item]) -> Self {
        let mut facts = FileFacts {
            decls: BTreeMap::new(),
            manual_eq: BTreeSet::new(),
            item_names: BTreeMap::new(),
            fn_names: BTreeMap::new(),
            root_spec_fns: BTreeMap::new(),
            declared_items: BTreeSet::new(),
        };
        for item in items {
            if let Item::Fn(func) = item {
                if has_trust_vc_spec_attr(&func.attrs) {
                    facts
                        .root_spec_fns
                        .insert(func.sig.ident.to_string(), func.clone());
                }
            }
        }
        facts.walk(items, &mut Vec::new());
        facts
    }

    fn name(&mut self, ident: &Ident) {
        *self.item_names.entry(ident.to_string()).or_default() += 1;
        self.declared_items.insert(ident.to_string());
    }

    fn fn_name(&mut self, ident: &Ident) {
        self.name(ident);
        *self.fn_names.entry(ident.to_string()).or_default() += 1;
    }

    fn decl(&mut self, ident: &Ident, module: &[String], item: Option<Item>) {
        self.decls
            .entry(ident.to_string())
            .or_default()
            .push((module.to_vec(), item));
    }

    fn walk(&mut self, items: &[Item], module: &mut Vec<String>) {
        for item in items {
            match item {
                Item::Fn(func) => self.fn_name(&func.sig.ident),
                Item::Struct(s) => {
                    self.name(&s.ident);
                    self.decl(&s.ident, module, Some(item.clone()));
                }
                Item::Enum(e) => {
                    self.name(&e.ident);
                    self.decl(&e.ident, module, Some(item.clone()));
                }
                Item::Union(u) => {
                    self.name(&u.ident);
                    self.decl(&u.ident, module, None);
                }
                Item::Type(t) => {
                    self.name(&t.ident);
                    self.decl(&t.ident, module, None);
                }
                Item::Trait(t) => {
                    self.name(&t.ident);
                    self.decl(&t.ident, module, None);
                    for trait_item in &t.items {
                        if let syn::TraitItem::Fn(method) = trait_item {
                            self.fn_name(&method.sig.ident);
                        }
                    }
                }
                Item::TraitAlias(t) => self.name(&t.ident),
                Item::Const(c) => self.name(&c.ident),
                Item::Static(s) => self.name(&s.ident),
                Item::Macro(m) => {
                    if let Some(ident) = &m.ident {
                        self.name(ident);
                    }
                }
                Item::ExternCrate(e) => {
                    let bound = e.rename.as_ref().map(|(_, r)| r).unwrap_or(&e.ident);
                    self.name(bound);
                    self.decl(bound, module, None);
                }
                Item::Use(u) => {
                    let mut bound = Vec::new();
                    use_bound_idents(&u.tree, &mut bound);
                    for ident in bound {
                        *self.item_names.entry(ident.to_string()).or_default() += 1;
                        self.decl(&ident, module, None);
                    }
                }
                Item::Impl(imp) => {
                    for impl_item in &imp.items {
                        if let syn::ImplItem::Fn(method) = impl_item {
                            self.fn_name(&method.sig.ident);
                        }
                    }
                    if let Some((_, trait_path, _)) = &imp.trait_ {
                        let is_eq = trait_path
                            .segments
                            .last()
                            .is_some_and(|seg| seg.ident == "PartialEq" || seg.ident == "Eq");
                        if is_eq {
                            if let Type::Path(tp) = &*imp.self_ty {
                                if let Some(last) = tp.path.segments.last() {
                                    self.manual_eq.insert(last.ident.to_string());
                                }
                            }
                        }
                    }
                }
                Item::Mod(m) => {
                    self.name(&m.ident);
                    if let Some((_, inner)) = &m.content {
                        module.push(m.ident.to_string());
                        self.walk(inner, module);
                        module.pop();
                    }
                }
                Item::ForeignMod(f) => {
                    for foreign in &f.items {
                        if let syn::ForeignItem::Fn(func) = foreign {
                            self.fn_name(&func.sig.ident);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    pub(crate) fn item_count(&self, name: &str) -> usize {
        self.item_names.get(name).copied().unwrap_or(0)
    }

    pub(crate) fn fn_count(&self, name: &str) -> usize {
        self.fn_names.get(name).copied().unwrap_or(0)
    }

    pub(crate) fn names_with_prefix(&self, prefix: &str) -> Option<String> {
        self.item_names
            .keys()
            .find(|name| name.starts_with(prefix))
            .cloned()
    }

    pub(crate) fn declares_scalar_name(&self) -> Option<&'static str> {
        ["int", "nat", "bool"]
            .into_iter()
            .find(|name| self.declared_items.contains(*name))
    }
}

fn use_bound_idents(tree: &syn::UseTree, out: &mut Vec<Ident>) {
    match tree {
        syn::UseTree::Path(p) => use_bound_idents(&p.tree, out),
        syn::UseTree::Name(n) => {
            if n.ident != "self" {
                out.push(n.ident.clone());
            }
        }
        syn::UseTree::Rename(r) => out.push(r.rename.clone()),
        syn::UseTree::Group(g) => {
            for item in &g.items {
                use_bound_idents(item, out);
            }
        }
        syn::UseTree::Glob(_) => {}
    }
}

pub(crate) fn has_trust_vc_spec_attr(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let segs: Vec<String> = attr
            .path()
            .segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect();
        matches!(attr.meta, Meta::Path(_)) && segs == ["trust_vc", "spec"]
    })
}

/// Outcome of checking one invocation.
pub(crate) type Checked = Result<Machine, Vec<String>>;

fn err_msg(err: &syn::Error) -> Vec<String> {
    err.clone().into_iter().map(|e| e.to_string()).collect()
}

/// Upstream `validate_ident`.
pub(crate) fn validate_ident(ident: &Ident) -> Result<(), String> {
    let text = ident.to_string();
    for kw in ["post", "instance", "tmp_tuple", "tmp_e", "tmp_assert"] {
        if text == kw {
            return Err(format!(
                "'{kw}' is a reserved identifier in state machine definitions"
            ));
        }
    }
    for prefix in ["param_token_", "original_field_", "update_tmp_"] {
        if text.starts_with(prefix) {
            return Err(format!(
                "identifiers starting with '{prefix}' are reserved identifiers in state machine definitions"
            ));
        }
    }
    Ok(())
}

fn path_segments(path: &syn::Path) -> Vec<String> {
    path.segments.iter().map(|s| s.ident.to_string()).collect()
}

fn attr_is_any_mode(attr: &Attribute) -> bool {
    match &attr.meta {
        Meta::Path(path) => {
            let segs = path_segments(path);
            segs.len() == 2
                && segs[0] == "verifier"
                && matches!(segs[1].as_str(), "spec" | "proof" | "exec")
        }
        _ => false,
    }
}

fn attr_is_polarity(attr: &Attribute) -> bool {
    match &attr.meta {
        Meta::List(list) => {
            let segs = path_segments(&list.path);
            segs.len() == 2
                && segs[0] == "verifier"
                && matches!(
                    segs[1].as_str(),
                    "accept_recursive_types"
                        | "reject_recursive_types"
                        | "reject_recursive_types_in_ground_variants"
                )
        }
        _ => false,
    }
}

fn is_doc_attr(attr: &Attribute) -> bool {
    matches!(&attr.meta, Meta::NameValue(nv) if nv.path.is_ident("doc"))
}

fn attr_text(attr: &Attribute) -> String {
    attr.to_token_stream().to_string()
}

enum FnAttrInfo {
    None,
    Invariant,
    Lemma(Ident),
}

fn parse_fn_attr_info(attrs: &[Attribute]) -> Result<FnAttrInfo, String> {
    let mut info = FnAttrInfo::None;
    for attr in attrs {
        if !matches!(attr.style, syn::AttrStyle::Outer) {
            continue;
        }
        match &attr.meta {
            Meta::Path(path) if path.is_ident("invariant") => {
                if !matches!(info, FnAttrInfo::None) {
                    return Err("conflicting attributes".to_string());
                }
                info = FnAttrInfo::Invariant;
            }
            Meta::List(list) if list.path.is_ident("inductive") => {
                let name: Ident = attr
                    .parse_args()
                    .map_err(|_| "expected transition name: #[inductive(name)]".to_string())?;
                if !matches!(info, FnAttrInfo::None) {
                    return Err("conflicting attributes".to_string());
                }
                info = FnAttrInfo::Lemma(name);
            }
            _ => {}
        }
    }
    Ok(info)
}

fn check_invariant_sig(func: &syn::ItemFn) -> Result<(), String> {
    if func.attrs.iter().any(attr_is_any_mode) {
        return Err(
            "an invariant fn is implied to be 'spec'; it should not be explicitly labelled"
                .to_string(),
        );
    }
    if func.sig.inputs.len() != 1 {
        return Err("an invariant function must take exactly 1 argument (self)".to_string());
    }
    match func.sig.inputs.first() {
        Some(syn::FnArg::Receiver(recv))
            if recv.mutability.is_none() && recv.colon_token.is_none() => {}
        _ => return Err("an invariant function must take 1 argument (self)".to_string()),
    }
    if !func.sig.generics.params.is_empty() {
        return Err("an invariant function must take 0 type arguments".to_string());
    }
    match &func.sig.output {
        syn::ReturnType::Type(_, ty) => match &**ty {
            Type::Path(tp) if tp.qself.is_none() && tp.path.is_ident("bool") => Ok(()),
            _ => Err("an invariant function must return a bool".to_string()),
        },
        syn::ReturnType::Default => Err("an invariant function must return a bool".to_string()),
    }
}

/// Parse + upstream well-formedness + D1a admission of one invocation body.
pub(crate) fn check_machine(tokens: TokenStream, facts: Option<&FileFacts>) -> Checked {
    let ast: MachineAst = syn::parse2(tokens).map_err(|e| err_msg(&e))?;
    let name = ast.name.clone();
    validate_ident(&name).map_err(|e| vec![e])?;
    let generics = match &ast.generics {
        Some(Err(err)) => return Err(err_msg(err)),
        Some(Ok(generics)) => Some(generics.clone()),
        None => None,
    };
    for attr in &ast.attrs {
        if !attr_is_polarity(attr) {
            return Err(vec!["the only attributes allowed here are verus_keep_ghost, verifier::accept_recursive_types, verifier::reject_recursive_types, and verifier::reject_recursive_types_in_ground_variants".to_string()]);
        }
    }
    let Some(fields_named) = ast.fields.clone() else {
        return Err(vec![
            "the 'fields' declaration was not found in the state machine definition".to_string(),
        ]);
    };

    let mut helper_fns: Vec<syn::ItemFn> = Vec::new();
    let mut transitions: Vec<TransitionAst> = Vec::new();
    let mut invariants: Vec<InvariantDef> = Vec::new();
    let mut lemmas: Vec<(syn::ItemFn, Ident)> = Vec::new();
    let mut labels: Vec<String> = Vec::new();
    for item in &ast.items {
        match item {
            Item::Fn(func) => match parse_fn_attr_info(&func.attrs).map_err(|e| vec![e])? {
                FnAttrInfo::None => helper_fns.push(func.clone()),
                FnAttrInfo::Invariant => {
                    check_invariant_sig(func).map_err(|e| vec![e])?;
                    invariants.push(InvariantDef { func: func.clone() });
                }
                FnAttrInfo::Lemma(target) => {
                    if func.attrs.iter().any(attr_is_any_mode) {
                        return Err(vec!["an inductivity lemma is implied to be 'proof'; it should not be explicitly labelled".to_string()]);
                    }
                    lemmas.push((func.clone(), target));
                }
            },
            Item::Macro(item_macro) if item_macro.ident.is_none() => {
                transitions.push(parse_transition(&item_macro.mac).map_err(|e| err_msg(&e))?);
            }
            Item::Type(_) | Item::Struct(_) | Item::Enum(_) => {
                let ident = match item {
                    Item::Type(t) => &t.ident,
                    Item::Struct(s) => &s.ident,
                    Item::Enum(e) => &e.ident,
                    _ => unreachable!("matched above"),
                };
                if ident != "Label" && ident != "InitLabel" {
                    return Err(vec!["state_machine macro only supports the declaration of a `Label` and `InitLabel` types".to_string()]);
                }
                labels.push(ident.to_string());
            }
            _ => return Err(vec!["this item is not supported".to_string()]),
        }
    }

    // to_fields
    let mut fields = Vec::new();
    for field in &fields_named.named {
        let Some(ident) = field.ident.clone() else {
            return Err(vec!["state machine field must have a name".to_string()]);
        };
        if !matches!(field.vis, syn::Visibility::Public(_)) {
            return Err(vec!["state machine field must be marked public".to_string()]);
        }
        if field.attrs.iter().any(attr_is_any_mode) {
            return Err(vec![
                "a state field is implied to be 'spec'; it should not be explicitly labelled"
                    .to_string(),
            ]);
        }
        validate_ident(&ident).map_err(|e| vec![e])?;
        for attr in &field.attrs {
            if attr.path().is_ident("sharding") {
                let msg =
                    "expected 1 argument as the sharding strategy, e.g., #[sharding(variable)]";
                let Meta::List(_) = &attr.meta else {
                    return Err(vec![msg.to_string()]);
                };
                let strategy: Ident = attr.parse_args().map_err(|_| vec![msg.to_string()])?;
                const KNOWN: &[&str] = &[
                    "variable",
                    "constant",
                    "multiset",
                    "set",
                    "bool",
                    "count",
                    "option",
                    "map",
                    "storage_option",
                    "storage_map",
                    "persistent_option",
                    "persistent_map",
                    "persistent_set",
                    "persistent_count",
                    "persistent_bool",
                    "not_tokenized",
                ];
                if !KNOWN.contains(&strategy.to_string().as_str()) {
                    return Err(vec![format!(
                        "unrecognized sharding strategy: '{strategy}'"
                    )]);
                }
                return Err(vec!["sharding strategy only makes sense for tokenized state machines; did you mean to use the tokenized_state_machine! macro?".to_string()]);
            }
        }
        fields.push(FieldDef {
            name: ident,
            ty: field.ty.clone(),
        });
    }

    // check_transitions
    let field_names: BTreeSet<String> = fields.iter().map(|f| f.name.to_string()).collect();
    let mut errors = Vec::new();
    let mut seen = BTreeSet::new();
    for tr in &transitions {
        if !seen.insert(tr.name.to_string()) {
            errors.push("duplicate item name".to_string());
        }
        errors.extend(check_transition(&field_names, tr));
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    for inv in &invariants {
        if !matches!(inv.func.vis, syn::Visibility::Public(_)) {
            return Err(vec!["#[invariant] fn must be be marked `pub` so it can called from the auto-generated `invariant` fn".to_string()]);
        }
    }

    // check_lemmas
    let lemma_defs = check_lemmas(&name, &transitions, &invariants, &lemmas)?;

    let machine = Machine {
        name,
        fields,
        transitions,
        invariants,
        lemmas: lemma_defs,
    };
    admit(
        &machine,
        &ast.attrs,
        generics.as_ref(),
        &labels,
        &helper_fns,
        facts,
    )
    .map_err(|e| vec![e])?;
    Ok(machine)
}

// ---------------------------------------------------------------------------
// check_transition (upstream transitions.rs)

struct IdentValidator<'a> {
    errors: Vec<String>,
    kind: TransitionKind,
    bound: &'a BTreeSet<String>,
    fields: &'a BTreeSet<String>,
}

impl<'ast> Visit<'ast> for IdentValidator<'_> {
    fn visit_ident(&mut self, node: &'ast Ident) {
        if node == "post" {
            self.errors
                .push("cannot refer directly to `post` in a transition definition".to_string());
        } else if node == "pre" {
            if self.kind == TransitionKind::Init {
                self.errors.push("cannot refer to `pre` in an 'init' routine; there is no previous state to refer to".to_string());
            }
        } else if node == "self" {
            self.errors.push("identifier `self` is meaningless in transition definition; use `pre` to refer to the previous state (in non-init transitions)".to_string());
        } else if let Err(err) = validate_ident(node) {
            self.errors.push(err);
        }
    }

    fn visit_expr_macro(&mut self, _node: &'ast syn::ExprMacro) {
        self.errors
            .push("macro not allowed in transition expression".to_string());
    }

    fn visit_expr(&mut self, node: &'ast Expr) {
        match node {
            Expr::Verbatim(_) => self
                .errors
                .push("Verus does not support this expression".to_string()),
            Expr::Path(path) => {
                if path.qself.is_none()
                    && path.path.segments.len() == 1
                    && path.path.leading_colon.is_none()
                {
                    let id = path.path.segments[0].ident.to_string();
                    if self.fields.contains(&id) && !self.bound.contains(&id) {
                        self.errors
                            .push(format!("Use `pre.{id}` to access this field's value"));
                    }
                }
                syn::visit::visit_expr(self, node);
            }
            _ => syn::visit::visit_expr(self, node),
        }
    }
}

fn validate_expr(
    e: &Expr,
    kind: TransitionKind,
    bound: &BTreeSet<String>,
    fields: &BTreeSet<String>,
) -> Result<(), Vec<String>> {
    let mut v = IdentValidator {
        errors: Vec::new(),
        kind,
        bound,
        fields,
    };
    v.visit_expr(e);
    if v.errors.is_empty() {
        Ok(())
    } else {
        Err(v.errors)
    }
}

fn validate_pat(p: &Pat, kind: TransitionKind) -> Result<(), Vec<String>> {
    let empty = BTreeSet::new();
    let mut v = IdentValidator {
        errors: Vec::new(),
        kind,
        bound: &empty,
        fields: &empty,
    };
    v.visit_pat(p);
    if v.errors.is_empty() {
        Ok(())
    } else {
        Err(v.errors)
    }
}

pub(crate) fn pattern_bound_idents(pat: &Pat) -> Vec<Ident> {
    struct Collect(Vec<Ident>);
    impl<'ast> Visit<'ast> for Collect {
        fn visit_pat_ident(&mut self, node: &'ast syn::PatIdent) {
            if !self.0.contains(&node.ident) {
                self.0.push(node.ident.clone());
            }
            syn::visit::visit_pat_ident(self, node);
        }
    }
    let mut c = Collect(Vec::new());
    c.visit_pat(pat);
    c.0
}

fn validate_stmt(
    ts: &TStmt,
    kind: TransitionKind,
    bound: &BTreeSet<String>,
    fields: &BTreeSet<String>,
) -> Result<(), Vec<String>> {
    match ts {
        TStmt::Block(_, stmts) => {
            for s in stmts {
                validate_stmt(s, kind, bound, fields)?;
            }
        }
        TStmt::Let {
            pat, expr, body, ..
        } => {
            validate_expr(expr, kind, bound, fields)?;
            validate_pat(pat, kind)?;
            let mut inner = bound.clone();
            for id in pattern_bound_idents(pat) {
                inner.insert(id.to_string());
            }
            validate_stmt(body, kind, &inner, fields)?;
        }
        TStmt::If { cond, thn, els, .. } => {
            validate_expr(cond, kind, bound, fields)?;
            validate_stmt(thn, kind, bound, fields)?;
            validate_stmt(els, kind, bound, fields)?;
        }
        TStmt::Match { expr, arms, .. } => {
            validate_expr(expr, kind, bound, fields)?;
            let mut per_arm = Vec::new();
            for (pat, guard, _) in arms {
                validate_pat(pat, kind)?;
                let mut inner = bound.clone();
                for id in pattern_bound_idents(pat) {
                    inner.insert(id.to_string());
                }
                if let Some(guard) = guard {
                    validate_expr(guard, kind, &inner, fields)?;
                }
                per_arm.push(inner);
            }
            for ((_, _, body), inner) in arms.iter().zip(per_arm) {
                validate_stmt(body, kind, &inner, fields)?;
            }
        }
        TStmt::Special { op, body, .. } => {
            validate_ident(&op.field).map_err(|e| vec![e])?;
            for e in &op.exprs {
                validate_expr(e, kind, bound, fields)?;
            }
            let mut inner = bound.clone();
            if let Some(pat) = &op.pat {
                validate_pat(pat, kind)?;
                for id in pattern_bound_idents(pat) {
                    inner.insert(id.to_string());
                }
            }
            validate_stmt(body, kind, &inner, fields)?;
        }
        TStmt::Require(_, e) | TStmt::Assert(_, e) => validate_expr(e, kind, bound, fields)?,
        TStmt::SubUpdate(_, f, subs, e) => {
            validate_ident(f).map_err(|e| vec![e])?;
            for sub in subs {
                match sub {
                    SubIdx::Field(id) => validate_ident(id).map_err(|e| vec![e])?,
                    SubIdx::Idx(e) => validate_expr(e, kind, bound, fields)?,
                }
            }
            validate_expr(e, kind, bound, fields)?;
        }
        TStmt::Update(_, f, e) | TStmt::Init(_, f, e) => {
            validate_ident(f).map_err(|e| vec![e])?;
            validate_expr(e, kind, bound, fields)?;
        }
    }
    Ok(())
}

fn check_fields_exist(fields: &BTreeSet<String>, ts: &TStmt, errors: &mut Vec<String>) {
    let mut missing = |f: &Ident| {
        if !fields.contains(&f.to_string()) {
            errors.push(format!("field '{f}' not found"));
        }
    };
    match ts {
        TStmt::Block(_, stmts) => {
            for s in stmts {
                check_fields_exist(fields, s, errors);
            }
        }
        TStmt::Special { op, body, .. } => {
            missing(&op.field);
            check_fields_exist(fields, body, errors);
        }
        TStmt::Let { body, .. } => check_fields_exist(fields, body, errors),
        TStmt::If { thn, els, .. } => {
            check_fields_exist(fields, thn, errors);
            check_fields_exist(fields, els, errors);
        }
        TStmt::Match { arms, .. } => {
            for (_, _, body) in arms {
                check_fields_exist(fields, body, errors);
            }
        }
        TStmt::Update(_, f, _) | TStmt::SubUpdate(_, f, _, _) | TStmt::Init(_, f, _) => missing(f),
        TStmt::Require(..) | TStmt::Assert(..) => {}
    }
}

fn special_not_variable(op: &SpecialOp) -> String {
    format!(
        "'{}' statement not allowed for field with sharding strategy 'variable'; use 'update' instead",
        op.op
    )
}

fn check_valid_ops(ts: &TStmt, readonly: bool, property: bool, errors: &mut Vec<String>) {
    match ts {
        TStmt::Block(_, stmts) => {
            for s in stmts {
                check_valid_ops(s, readonly, property, errors);
            }
        }
        TStmt::Special { op, body, .. } => {
            errors.push(special_not_variable(op));
            if readonly && op.is_modifier() {
                errors.push(format!(
                    "'{}' statement not allowed in readonly transition",
                    op.op
                ));
            }
            if property && op.is_modifier() {
                errors.push(format!(
                    "'{}' statement not allowed in 'property' definition",
                    op.op
                ));
            }
            if !readonly && !property && op.only_in_readonly_or_property() {
                errors.push(format!(
                    "'{}' statement only allowed in 'readonly' transition or 'property' definition",
                    op.op
                ));
            }
            check_valid_ops(body, readonly, property, errors);
        }
        TStmt::Let { body, .. } => check_valid_ops(body, readonly, property, errors),
        TStmt::If { thn, els, .. } => {
            check_valid_ops(thn, readonly, property, errors);
            check_valid_ops(els, readonly, property, errors);
        }
        TStmt::Match { arms, .. } => {
            for (_, _, body) in arms {
                check_valid_ops(body, readonly, property, errors);
            }
        }
        TStmt::Require(..) | TStmt::Assert(..) => {}
        TStmt::Init(..) => {
            errors.push("'init' statement not allowed outside 'init' routine".to_string())
        }
        TStmt::Update(..) | TStmt::SubUpdate(..) => {
            if readonly {
                errors.push("'update' statement not allowed in readonly transition".to_string());
            }
            if property {
                errors.push("'update' statement not allowed in property definition".to_string());
            }
        }
    }
}

fn check_valid_ops_init(ts: &TStmt, errors: &mut Vec<String>) {
    match ts {
        TStmt::Block(_, stmts) => {
            for s in stmts {
                check_valid_ops_init(s, errors);
            }
        }
        TStmt::Special { op, body, .. } => {
            errors.push(format!(
                "'{}' statement not allowed in initialization; use 'init' instead",
                op.op
            ));
            check_valid_ops_init(body, errors);
        }
        TStmt::Let { body, .. } => check_valid_ops_init(body, errors),
        TStmt::If { thn, els, .. } => {
            check_valid_ops_init(thn, errors);
            check_valid_ops_init(els, errors);
        }
        TStmt::Match { arms, .. } => {
            for (_, _, body) in arms {
                check_valid_ops_init(body, errors);
            }
        }
        TStmt::Require(..) | TStmt::Init(..) => {}
        TStmt::Assert(..) => {
            errors.push("'assert' statement not allowed in initialization".to_string())
        }
        TStmt::Update(..) | TStmt::SubUpdate(..) => errors.push(
            "'update' statement not allowed in initialization; use 'init' instead".to_string(),
        ),
    }
}

/// Upstream `check_exactly_one_init_rec`: `Ok(true)` when the field is
/// initialized on this subtree.
fn init_once(field: &str, ts: &TStmt) -> Result<bool, String> {
    match ts {
        TStmt::Block(_, stmts) => {
            let mut seen = false;
            for s in stmts {
                if init_once(field, s)? {
                    if seen {
                        return Err(format!(
                            "field '{field}' might be initialized multiple times"
                        ));
                    }
                    seen = true;
                }
            }
            Ok(seen)
        }
        TStmt::Let { body, .. } => init_once(field, body),
        TStmt::If { thn, els, .. } => match (init_once(field, thn)?, init_once(field, els)?) {
            (true, true) => Ok(true),
            (false, false) => Ok(false),
            (true, false) => Err(format!("for initialization, both branches of an if-statement must initialize the same fields; the else-branch does not initialize '{field}'")),
            (false, true) => Err(format!("for initialization, both branches of an if-statement must initialize the same fields; the if-branch does not initialize '{field}'")),
        },
        TStmt::Match { arms, .. } => {
            let mut first = None;
            for (_, _, body) in arms {
                let this = init_once(field, body)?;
                match first {
                    None => first = Some(this),
                    Some(f) if f != this => return Err(format!("for initialization, all branches of a match-statement must initialize the same fields; this branch does not initialize '{field}'")),
                    Some(_) => {}
                }
            }
            Ok(first.unwrap_or(false))
        }
        TStmt::Special { .. } => Ok(false),
        TStmt::Init(_, f, _) => Ok(f == field),
        TStmt::Require(..) | TStmt::Assert(..) | TStmt::Update(..) | TStmt::SubUpdate(..) => {
            Ok(false)
        }
    }
}

fn update_at_most_once(field: &str, ts: &TStmt) -> Result<bool, String> {
    match ts {
        TStmt::Block(_, stmts) => {
            let mut seen = false;
            for s in stmts {
                if update_at_most_once(field, s)? {
                    if seen {
                        return Err(format!("field '{field}' might be updated multiple times"));
                    }
                    seen = true;
                }
            }
            Ok(seen)
        }
        TStmt::Let { body, .. } | TStmt::Special { body, .. } => update_at_most_once(field, body),
        TStmt::If { thn, els, .. } => {
            let a = update_at_most_once(field, thn)?;
            let b = update_at_most_once(field, els)?;
            Ok(a || b)
        }
        TStmt::Match { arms, .. } => {
            let mut any = false;
            for (_, _, body) in arms {
                any |= update_at_most_once(field, body)?;
            }
            Ok(any)
        }
        TStmt::Update(_, f, _) => Ok(f == field),
        _ => Ok(false),
    }
}

fn let_shadowing(ts: &TStmt, ids: &mut Vec<String>, errors: &mut Vec<String>) {
    let new_ids: Vec<Ident> = match ts {
        TStmt::Let { pat, .. } => pattern_bound_idents(pat),
        TStmt::Special { op, .. } => op
            .pat
            .as_ref()
            .map(pattern_bound_idents)
            .unwrap_or_default(),
        TStmt::Match { arms, .. } => arms
            .iter()
            .flat_map(|(pat, _, _)| pattern_bound_idents(pat))
            .collect(),
        _ => Vec::new(),
    };
    for id in new_ids {
        let s = id.to_string();
        if ids.contains(&s) {
            errors.push(
                "state machine transitions forbid multiple bound variables with the same name"
                    .to_string(),
            );
        } else {
            ids.push(s);
        }
    }
    match ts {
        TStmt::Block(_, stmts) => {
            for s in stmts {
                let_shadowing(s, ids, errors);
            }
        }
        TStmt::Let { body, .. } | TStmt::Special { body, .. } => let_shadowing(body, ids, errors),
        TStmt::If { thn, els, .. } => {
            let_shadowing(thn, ids, errors);
            let_shadowing(els, ids, errors);
        }
        TStmt::Match { arms, .. } => {
            for (_, _, body) in arms {
                let_shadowing(body, ids, errors);
            }
        }
        _ => {}
    }
}

fn birds_eye(ts: &TStmt, is_init: bool, errors: &mut Vec<String>) {
    match ts {
        TStmt::Let { kind, body, .. } => {
            if *kind == LetKind::BirdsEye {
                errors.push("`birds_eye` only makes sense for tokenized state machines; did you mean to use the tokenized_state_machine! macro?".to_string());
                if is_init {
                    errors.push("`birds_eye` has no effect in an init! definition".to_string());
                }
            }
            birds_eye(body, is_init, errors);
        }
        TStmt::Block(_, stmts) => {
            for s in stmts {
                birds_eye(s, is_init, errors);
            }
        }
        TStmt::Special { body, .. } => birds_eye(body, is_init, errors),
        TStmt::If { thn, els, .. } => {
            birds_eye(thn, is_init, errors);
            birds_eye(els, is_init, errors);
        }
        TStmt::Match { arms, .. } => {
            for (_, _, body) in arms {
                birds_eye(body, is_init, errors);
            }
        }
        _ => {}
    }
}

fn super_path_errors(ty: &Type, errors: &mut Vec<String>) {
    struct SuperVisitor<'a>(&'a mut Vec<String>);
    impl<'ast> Visit<'ast> for SuperVisitor<'_> {
        fn visit_macro(&mut self, _node: &'ast syn::Macro) {
            self.0
                .push("state machine error: macro not allowed here".to_string());
        }
        fn visit_path(&mut self, node: &'ast syn::Path) {
            if node.segments.first().is_some_and(|s| s.ident == "super") {
                self.0
                    .push("state machine error: `super::` path not allowed here".to_string());
            }
            syn::visit::visit_path(self, node);
        }
    }
    SuperVisitor(errors).visit_type(ty);
}

fn check_transition(fields: &BTreeSet<String>, tr: &TransitionAst) -> Vec<String> {
    // validate_idents_transition (early return, like upstream `?`)
    if let Err(e) = validate_ident(&tr.name) {
        return vec![e];
    }
    let mut bound = BTreeSet::new();
    for p in &tr.params {
        if let Err(e) = validate_ident(&p.name) {
            return vec![e];
        }
        bound.insert(p.name.to_string());
    }
    if let Err(errs) = validate_stmt(&tr.body, tr.kind, &bound, fields) {
        return errs;
    }

    let mut errors = Vec::new();
    check_fields_exist(fields, &tr.body, &mut errors);
    if !errors.is_empty() {
        return errors;
    }
    match tr.kind {
        TransitionKind::Readonly => check_valid_ops(&tr.body, true, false, &mut errors),
        TransitionKind::Property => check_valid_ops(&tr.body, false, true, &mut errors),
        TransitionKind::Transition => {
            check_valid_ops(&tr.body, false, false, &mut errors);
            for f in fields {
                if let Err(e) = update_at_most_once(f, &tr.body) {
                    errors.push(e);
                }
            }
        }
        TransitionKind::Init => {
            check_valid_ops_init(&tr.body, &mut errors);
            if errors.is_empty() {
                for f in fields {
                    match init_once(f, &tr.body) {
                        Ok(true) => {}
                        Ok(false) => errors.push(format!(
                            "itialization procedure does not initialize field '{f}'"
                        )),
                        Err(e) => errors.push(e),
                    }
                }
            }
        }
    }
    let mut ids: Vec<String> = tr.params.iter().map(|p| p.name.to_string()).collect();
    let_shadowing(&tr.body, &mut ids, &mut errors);
    birds_eye(&tr.body, tr.kind == TransitionKind::Init, &mut errors);
    for p in &tr.params {
        super_path_errors(&p.ty, &mut errors);
    }
    errors
}

// ---------------------------------------------------------------------------
// check_lemmas (upstream lemmas.rs)

fn expected_lemma_params(tr: &TransitionAst) -> Vec<(String, String)> {
    let mut v = Vec::new();
    if tr.kind == TransitionKind::Transition {
        v.push(("pre".to_string(), "Self".to_string()));
    }
    v.push(("post".to_string(), "Self".to_string()));
    for p in &tr.params {
        v.push((p.name.to_string(), p.ty.to_token_stream().to_string()));
    }
    v
}

fn ty_to_string(ty: &str) -> String {
    ty.replace("< ", "<")
        .replace(" <", "<")
        .replace("> ", ">")
        .replace(" >", ">")
        .replace(":: ", "::")
        .replace(" ::", "::")
}

fn lemma_params_match(expected: &[(String, String)], func: &syn::ItemFn) -> bool {
    let inputs: Vec<&syn::FnArg> = func.sig.inputs.iter().collect();
    for (i, arg) in inputs.iter().enumerate() {
        if i >= expected.len() {
            return false;
        }
        match arg {
            syn::FnArg::Receiver(_) => return false,
            syn::FnArg::Typed(pt) => {
                if !pt.attrs.is_empty() {
                    return false;
                }
                match &*pt.pat {
                    Pat::Ident(pi)
                        if pi.attrs.is_empty()
                            && pi.by_ref.is_none()
                            && pi.mutability.is_none()
                            && pi.subpat.is_none()
                            && pi.ident == expected[i].0 => {}
                    _ => return false,
                }
                if pt.ty.to_token_stream().to_string() != expected[i].1 {
                    return false;
                }
            }
        }
    }
    inputs.len() == expected.len()
}

fn check_lemmas(
    machine_name: &Ident,
    transitions: &[TransitionAst],
    invariants: &[InvariantDef],
    lemmas: &[(syn::ItemFn, Ident)],
) -> Result<Vec<LemmaDef>, Vec<String>> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for (func, target) in lemmas {
        let name = target.to_string();
        if !seen.insert(name.clone()) {
            return Err(vec![format!(
                "duplicate 'inductive' lemma for transition `{name}`"
            )]);
        }
        let Some(tr) = transitions.iter().find(|t| t.name == name) else {
            return Err(vec![format!("could not find transition `{name}`")]);
        };
        let kind = match tr.kind {
            TransitionKind::Readonly => {
                return Err(vec![
                    "'inductive' lemma does not make sense for a 'readonly' transition".to_string(),
                ])
            }
            TransitionKind::Property => {
                return Err(vec![
                    "'inductive' lemma does not make sense for a 'property' definition".to_string(),
                ])
            }
            TransitionKind::Init => LemmaKind::Init,
            TransitionKind::Transition => LemmaKind::Transition,
        };
        if !func.sig.generics.params.is_empty() {
            return Err(vec![
                "'inductive' lemma should have no generic parameters".to_string()
            ]);
        }
        if !matches!(func.sig.output, syn::ReturnType::Default) {
            return Err(vec![
                "'inductive' lemma should have no return type".to_string()
            ]);
        }
        let expected = expected_lemma_params(tr);
        if !lemma_params_match(&expected, func) {
            let rendered = expected
                .iter()
                .map(|(n, t)| format!("{n}: {}", ty_to_string(t)))
                .collect::<Vec<_>>()
                .join(", ");
            return Err(vec![format!(
                "params for 'inductive' lemma should be: `{rendered}`"
            )]);
        }
        out.push(LemmaDef {
            func: func.clone(),
            target: target.clone(),
            kind,
        });
    }
    if !invariants.is_empty() {
        let mut msgs = Vec::new();
        for tr in transitions {
            if matches!(tr.kind, TransitionKind::Init | TransitionKind::Transition)
                && !seen.contains(&tr.name.to_string())
            {
                let mut params = Vec::new();
                if tr.kind == TransitionKind::Transition {
                    params.push("pre: Self".to_string());
                }
                params.push("post: Self".to_string());
                for p in &tr.params {
                    params.push(format!(
                        "{}: {}",
                        p.name,
                        ty_to_string(&p.ty.to_token_stream().to_string())
                    ));
                }
                msgs.push(format!(
                    " #[inductive({n})]\n fn {n}_inductive({}) {{ }}\n",
                    params.join(", "),
                    n = tr.name
                ));
            }
        }
        if !msgs.is_empty() {
            let _ = machine_name;
            return Err(vec![format!(
                "missing inductiveness proofs for {} transition(s); try adding the following stubs:\n\n{}",
                msgs.len(),
                msgs.join("\n")
            )]);
        }
    }
    for lemma in &out {
        if let Some(syn::Stmt::Expr(Expr::Call(call), Some(_))) = lemma.func.block.stmts.first() {
            if let Expr::Path(p) = &*call.func {
                if p.path.is_ident("requires") || p.path.is_ident("ensures") {
                    return Err(vec!["header statement here was probably a mistake: in an inductiveness lemma, the precondition and postcondition are implicit, generated by the macro".to_string()]);
                }
            }
        }
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// D1a admission

/// Scalar/datatype classification of an admitted type.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum TyClass {
    Int,
    Nat,
    Bool,
    /// Bare name of an admitted file-local datatype (or, on the proc-macro
    /// lane, an unchecked path).
    Data(String),
}

const MACHINE_INTS: &[&str] = &[
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
];
const COLLECTIONS: &[&str] = &["Seq", "Set", "Map", "Multiset"];

fn ty_string(ty: &Type) -> String {
    ty_to_string(&ty.to_token_stream().to_string())
}

enum TyRefusal {
    Collection,
    MachineInt,
    Nat,
    Other,
}

fn classify_type(
    ty: &Type,
    facts: Option<&FileFacts>,
    allow_nat: bool,
) -> Result<TyClass, TyRefusal> {
    let Type::Path(tp) = ty else {
        return Err(TyRefusal::Other);
    };
    if tp.qself.is_some() {
        return Err(TyRefusal::Other);
    }
    let segs: Vec<&syn::PathSegment> = tp.path.segments.iter().collect();
    let last = segs.last().ok_or(TyRefusal::Other)?;
    let last_name = last.ident.to_string();
    if COLLECTIONS.contains(&last_name.as_str()) {
        return Err(TyRefusal::Collection);
    }
    if segs.iter().any(|s| !s.arguments.is_empty()) {
        return Err(TyRefusal::Other);
    }
    if segs.len() == 1 && tp.path.leading_colon.is_none() {
        match last_name.as_str() {
            "int" => return Ok(TyClass::Int),
            "bool" => return Ok(TyClass::Bool),
            "nat" => {
                return if allow_nat {
                    Ok(TyClass::Nat)
                } else {
                    Err(TyRefusal::Nat)
                }
            }
            name if MACHINE_INTS.contains(&name) => return Err(TyRefusal::MachineInt),
            _ => {}
        }
    }
    if tp.path.leading_colon.is_some() {
        return Err(TyRefusal::Other);
    }
    let names: Vec<String> = segs.iter().map(|s| s.ident.to_string()).collect();
    match facts {
        None => {
            if names.iter().any(|n| n == "super" || n == "self") {
                return Err(TyRefusal::Other);
            }
            Ok(TyClass::Data(last_name))
        }
        Some(facts) => {
            admitted_datatype(facts, &names, &mut BTreeSet::new()).map_err(|_| TyRefusal::Other)
        }
    }
}

/// Resolve a datatype path (`S`, `m::S`, `crate::m::S`) to an admitted
/// file-local datatype.
fn admitted_datatype(
    facts: &FileFacts,
    path: &[String],
    visiting: &mut BTreeSet<String>,
) -> Result<TyClass, ()> {
    let mut path = path.to_vec();
    if path.first().is_some_and(|s| s == "crate") {
        path.remove(0);
    }
    let (name, module) = path.split_last().ok_or(())?;
    if module
        .iter()
        .any(|s| s == "self" || s == "super" || s == "crate")
    {
        return Err(());
    }
    let decls = facts.decls.get(name).ok_or(())?;
    if decls.len() != 1 {
        return Err(());
    }
    let (decl_module, item) = &decls[0];
    if decl_module.as_slice() != module {
        return Err(());
    }
    let item = item.as_ref().ok_or(())?;
    if facts.manual_eq.contains(name) || name.starts_with(GENERATED_PREFIX) {
        return Err(());
    }
    if !visiting.insert(name.clone()) {
        return Err(()); // recursive
    }
    let field_types: Vec<Type> = match item {
        Item::Struct(s) => {
            if !s.generics.params.is_empty() {
                return Err(());
            }
            match &s.fields {
                syn::Fields::Named(named) => named.named.iter().map(|f| f.ty.clone()).collect(),
                syn::Fields::Unit => Vec::new(),
                syn::Fields::Unnamed(_) => return Err(()),
            }
        }
        Item::Enum(e) => {
            if !e.generics.params.is_empty() {
                return Err(());
            }
            e.variants
                .iter()
                .flat_map(|v| v.fields.iter().map(|f| f.ty.clone()))
                .collect()
        }
        _ => return Err(()),
    };
    for fty in &field_types {
        match fty {
            Type::Path(tp) if tp.qself.is_none() && tp.path.leading_colon.is_none() => {
                if tp.path.segments.iter().any(|s| !s.arguments.is_empty()) {
                    return Err(());
                }
                let names: Vec<String> = tp
                    .path
                    .segments
                    .iter()
                    .map(|s| s.ident.to_string())
                    .collect();
                if names.len() == 1 && (names[0] == "int" || names[0] == "bool") {
                    continue;
                }
                // Field types are written relative to the declaring module.
                let mut full = if names.first().is_some_and(|n| n == "crate") {
                    names.clone()
                } else {
                    let mut full = decl_module.clone();
                    full.extend(names.clone());
                    full
                };
                if full.first().is_some_and(|n| n == "crate") {
                    full.remove(0);
                }
                admitted_datatype(facts, &full, visiting)?;
            }
            _ => return Err(()),
        }
    }
    visiting.remove(name);
    Ok(TyClass::Data(name.clone()))
}

struct DatatypeShape {
    /// Struct: named field -> type path (module-relative resolved).
    struct_fields: Option<Vec<(String, Vec<String>)>>,
    /// Enum: variant -> (kind, arity, named fields)
    variants: Vec<(String, VariantShape)>,
}

#[derive(Clone)]
enum VariantShape {
    Unit,
    Tuple(usize),
    Named(Vec<String>),
}

fn datatype_shape(facts: &FileFacts, name: &str) -> Option<DatatypeShape> {
    let decls = facts.decls.get(name)?;
    let (module, item) = decls.first()?;
    match item.as_ref()? {
        Item::Struct(s) => {
            let fields = match &s.fields {
                syn::Fields::Named(named) => named
                    .named
                    .iter()
                    .filter_map(|f| {
                        let ident = f.ident.as_ref()?.to_string();
                        let Type::Path(tp) = &f.ty else { return None };
                        let names: Vec<String> = tp
                            .path
                            .segments
                            .iter()
                            .map(|s| s.ident.to_string())
                            .collect();
                        let full = if names.len() == 1 && (names[0] == "int" || names[0] == "bool")
                        {
                            names
                        } else if names.first().is_some_and(|n| n == "crate") {
                            names[1..].to_vec()
                        } else {
                            let mut full = module.clone();
                            full.extend(names);
                            full
                        };
                        Some((ident, full))
                    })
                    .collect(),
                _ => Vec::new(),
            };
            Some(DatatypeShape {
                struct_fields: Some(fields),
                variants: Vec::new(),
            })
        }
        Item::Enum(e) => Some(DatatypeShape {
            struct_fields: None,
            variants: e
                .variants
                .iter()
                .map(|v| {
                    let shape = match &v.fields {
                        syn::Fields::Unit => VariantShape::Unit,
                        syn::Fields::Unnamed(u) => VariantShape::Tuple(u.unnamed.len()),
                        syn::Fields::Named(n) => VariantShape::Named(
                            n.named
                                .iter()
                                .filter_map(|f| f.ident.as_ref().map(|i| i.to_string()))
                                .collect(),
                        ),
                    };
                    (v.ident.to_string(), shape)
                })
                .collect(),
        }),
        _ => None,
    }
}

fn field_refusal(field: &FieldDef, why: TyRefusal) -> String {
    let t = ty_string(&field.ty);
    let f = &field.name;
    match why {
        TyRefusal::Collection => format!("field `{f}` has collection type `{t}`; collection-valued fields need extensional equality and are not yet supported"),
        TyRefusal::MachineInt => format!("field `{f}` has machine-integer type `{t}`; DSL arithmetic over machine integers is not modeled as mathematical and is not yet supported"),
        TyRefusal::Nat => format!("field `{f}` has type `nat`; nat-typed state fields carry no range fact in this engine and are not yet supported"),
        TyRefusal::Other => format!("field `{f}` has type `{t}`, which is not a file-local datatype admitted by D1a (generic, recursive, float-bearing, hand-written PartialEq, ambiguous bare name, or unknown)"),
    }
}

const RESERVED_NAMES: &[&str] = &["pre", "post", "self", "Self"];

fn check_binding_name(ident: &Ident, called: &BTreeSet<String>) -> Result<(), String> {
    let text = ident.to_string();
    if RESERVED_NAMES.contains(&text.as_str()) {
        return Err(format!("`{text}` is reserved (pre/post/self/Self)"));
    }
    if text.starts_with(GENERATED_PREFIX) {
        return Err(format!(
            "generated item `{text}` collides with an existing item"
        ));
    }
    if called.contains(&text) {
        return Err(format!(
            "name `{text}` is both a parameter/let and a called function"
        ));
    }
    Ok(())
}

/// Names of functions called anywhere in the transition's expressions.
fn called_fn_names(ts: &TStmt, out: &mut BTreeSet<String>) {
    struct Calls<'a>(&'a mut BTreeSet<String>);
    impl<'ast> Visit<'ast> for Calls<'_> {
        fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
            if let Expr::Path(p) = &*node.func {
                if let Some(last) = p.path.segments.last() {
                    self.0.insert(last.ident.to_string());
                }
            }
            syn::visit::visit_expr_call(self, node);
        }
    }
    for_each_expr(ts, &mut |e| Calls(out).visit_expr(e));
}

fn for_each_expr(ts: &TStmt, f: &mut dyn FnMut(&Expr)) {
    match ts {
        TStmt::Block(_, stmts) => {
            for s in stmts {
                for_each_expr(s, f);
            }
        }
        TStmt::Let { expr, body, .. } => {
            f(expr);
            for_each_expr(body, f);
        }
        TStmt::If { cond, thn, els, .. } => {
            f(cond);
            for_each_expr(thn, f);
            for_each_expr(els, f);
        }
        TStmt::Match { expr, arms, .. } => {
            f(expr);
            for (_, guard, body) in arms {
                if let Some(g) = guard {
                    f(g);
                }
                for_each_expr(body, f);
            }
        }
        TStmt::Require(_, e) | TStmt::Assert(_, e) => f(e),
        TStmt::Update(_, _, e) | TStmt::Init(_, _, e) => f(e),
        TStmt::SubUpdate(_, _, subs, e) => {
            for s in subs {
                if let SubIdx::Idx(i) = s {
                    f(i);
                }
            }
            f(e);
        }
        TStmt::Special { op, body, .. } => {
            for e in &op.exprs {
                f(e);
            }
            for_each_expr(body, f);
        }
    }
}

struct ExprScope<'a> {
    kind: TransitionKind,
    names: BTreeSet<String>,
    fields: &'a BTreeMap<String, TyClass>,
    facts: Option<&'a FileFacts>,
}

fn expr_text(e: &impl ToTokens) -> String {
    let text = e.to_token_stream().to_string();
    if text.len() > 80 {
        format!(
            "{}…",
            &text[..text.char_indices().nth(77).map_or(text.len(), |c| c.0)]
        )
    } else {
        text
    }
}

fn unsupported_expr(e: &impl ToTokens) -> String {
    format!(
        "expression form `{}` is not supported in a D1a transition body",
        expr_text(e)
    )
}

/// Resolve a value path to an admitted enum variant; returns its shape.
fn resolve_variant(scope: &ExprScope, path: &syn::Path) -> Option<VariantShape> {
    let facts = scope.facts?;
    if path.leading_colon.is_some() || path.segments.iter().any(|s| !s.arguments.is_empty()) {
        return None;
    }
    let names: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    let (variant, ty_path) = names.split_last()?;
    if ty_path.is_empty() {
        return None;
    }
    let TyClass::Data(name) = admitted_datatype(facts, ty_path, &mut BTreeSet::new()).ok()? else {
        return None;
    };
    let shape = datatype_shape(facts, &name)?;
    shape
        .variants
        .iter()
        .find(|(v, _)| v == variant)
        .map(|(_, s)| s.clone())
}

fn check_expr(e: &Expr, scope: &ExprScope) -> Result<(), String> {
    match e {
        Expr::Lit(lit) => match &lit.lit {
            syn::Lit::Bool(_) => Ok(()),
            syn::Lit::Int(i) if i.suffix().is_empty() => Ok(()),
            _ => Err(unsupported_expr(e)),
        },
        Expr::Paren(p) => check_expr(&p.expr, scope),
        Expr::Group(g) => check_expr(&g.expr, scope),
        Expr::Unary(u) => match u.op {
            syn::UnOp::Not(_) | syn::UnOp::Neg(_) => check_expr(&u.expr, scope),
            _ => Err(unsupported_expr(e)),
        },
        Expr::Binary(b) => {
            use syn::BinOp::*;
            match b.op {
                Add(_) | Sub(_) | Mul(_) | Eq(_) | Ne(_) | Lt(_) | Le(_) | Gt(_) | Ge(_)
                | And(_) | Or(_) => {
                    check_expr(&b.left, scope)?;
                    check_expr(&b.right, scope)
                }
                _ => Err(unsupported_expr(e)),
            }
        }
        Expr::If(expr_if) => {
            check_expr(&expr_if.cond, scope)?;
            check_single_expr_block(&expr_if.then_branch, scope, e)?;
            match &expr_if.else_branch {
                None => Err(unsupported_expr(e)),
                Some((_, els)) => match &**els {
                    Expr::If(_) => check_expr(els, scope),
                    Expr::Block(b) if b.attrs.is_empty() && b.label.is_none() => {
                        check_single_expr_block(&b.block, scope, e)
                    }
                    _ => Err(unsupported_expr(e)),
                },
            }
        }
        Expr::Path(p) => {
            if p.qself.is_some() || !p.attrs.is_empty() {
                return Err(unsupported_expr(e));
            }
            if let Some(ident) = p.path.get_ident() {
                let name = ident.to_string();
                if name == "pre" {
                    return Err("`pre` may only be used as `pre.<field>`".to_string());
                }
                if scope.names.contains(&name) {
                    return Ok(());
                }
                return Err(unsupported_expr(e));
            }
            match resolve_variant(scope, &p.path) {
                Some(VariantShape::Unit) => Ok(()),
                _ if scope.facts.is_none() => Ok(()),
                _ => Err(unsupported_expr(e)),
            }
        }
        Expr::Field(field) => {
            let ty = field_access_type(e, scope)?;
            let _ = (ty, field);
            Ok(())
        }
        Expr::Call(call) => {
            let Expr::Path(fp) = &*call.func else {
                return Err(unsupported_expr(e));
            };
            if fp.qself.is_some() {
                return Err(unsupported_expr(e));
            }
            for arg in &call.args {
                check_expr(arg, scope)?;
            }
            let names: Vec<String> = fp
                .path
                .segments
                .iter()
                .map(|s| s.ident.to_string())
                .collect();
            let plain_fn = fp.path.leading_colon.is_none()
                && fp.path.segments.iter().all(|s| s.arguments.is_empty())
                && (names.len() == 1
                    || (names.len() == 2 && (names[0] == "crate" || names[0] == "self")));
            let last = names.last().cloned().unwrap_or_default();
            if plain_fn && check_spec_fn_call(&last, call.args.len(), scope) {
                return Ok(());
            }
            if let Some(VariantShape::Tuple(n)) = resolve_variant(scope, &fp.path) {
                if n == call.args.len() {
                    return Ok(());
                }
            }
            if scope.facts.is_none() {
                return Ok(());
            }
            Err(format!("call to `{last}` is not supported: only file-root #[trust_vc::spec] fns with int/bool/admitted-datatype signatures"))
        }
        Expr::Struct(s) => {
            if s.rest.is_some() || s.dot2_token.is_some() || s.qself.is_some() {
                return Err(unsupported_expr(e));
            }
            for fv in &s.fields {
                check_expr(&fv.expr, scope)?;
            }
            let Some(facts) = scope.facts else {
                return Ok(());
            };
            let names: Vec<String> = s
                .path
                .segments
                .iter()
                .map(|x| x.ident.to_string())
                .collect();
            if s.path.leading_colon.is_some()
                || s.path.segments.iter().any(|x| !x.arguments.is_empty())
            {
                return Err(unsupported_expr(e));
            }
            let written: BTreeSet<String> = s
                .fields
                .iter()
                .map(|fv| match &fv.member {
                    syn::Member::Named(n) => n.to_string(),
                    syn::Member::Unnamed(i) => i.index.to_string(),
                })
                .collect();
            if written.len() != s.fields.len() {
                return Err(unsupported_expr(e));
            }
            let expected: Option<BTreeSet<String>> =
                match admitted_datatype(facts, &names, &mut BTreeSet::new()) {
                    Ok(TyClass::Data(name)) => datatype_shape(facts, &name)
                        .and_then(|shape| shape.struct_fields)
                        .map(|fields| fields.into_iter().map(|(n, _)| n).collect()),
                    _ => match resolve_variant(scope, &s.path) {
                        Some(VariantShape::Named(fields)) => Some(fields.into_iter().collect()),
                        _ => None,
                    },
                };
            match expected {
                Some(expected) if expected == written => Ok(()),
                _ => Err(unsupported_expr(e)),
            }
        }
        _ => Err(unsupported_expr(e)),
    }
}

fn check_single_expr_block(
    block: &syn::Block,
    scope: &ExprScope,
    whole: &Expr,
) -> Result<(), String> {
    match block.stmts.as_slice() {
        [syn::Stmt::Expr(inner, None)] => check_expr(inner, scope),
        _ => Err(unsupported_expr(whole)),
    }
}

/// The type of `pre.f(.g)*`, refusing anything else.
fn field_access_type(e: &Expr, scope: &ExprScope) -> Result<TyClass, String> {
    let Expr::Field(field) = e else {
        return Err(unsupported_expr(e));
    };
    let syn::Member::Named(member) = &field.member else {
        return Err(unsupported_expr(e));
    };
    match &*field.base {
        Expr::Path(p) if p.path.is_ident("pre") && p.qself.is_none() => {
            if scope.kind == TransitionKind::Init {
                return Err(unsupported_expr(e));
            }
            scope
                .fields
                .get(&member.to_string())
                .cloned()
                .ok_or_else(|| unsupported_expr(e))
        }
        base @ Expr::Field(_) => {
            let base_ty = field_access_type(base, scope)?;
            let TyClass::Data(name) = base_ty else {
                return Err(unsupported_expr(e));
            };
            let Some(facts) = scope.facts else {
                return Ok(TyClass::Data(String::new()));
            };
            let shape = datatype_shape(facts, &name).ok_or_else(|| unsupported_expr(e))?;
            let fields = shape.struct_fields.ok_or_else(|| unsupported_expr(e))?;
            let member_name = member.to_string();
            let (_, path) = fields
                .iter()
                .find(|(n, _)| *n == member_name)
                .ok_or_else(|| unsupported_expr(e))?;
            if path.len() == 1 && path[0] == "int" {
                return Ok(TyClass::Int);
            }
            if path.len() == 1 && path[0] == "bool" {
                return Ok(TyClass::Bool);
            }
            admitted_datatype(facts, path, &mut BTreeSet::new()).map_err(|_| unsupported_expr(e))
        }
        _ => Err(unsupported_expr(e)),
    }
}

fn spec_sig_type_ok(ty: &Type, facts: &FileFacts) -> bool {
    matches!(
        classify_type(ty, Some(facts), false),
        Ok(TyClass::Int | TyClass::Bool | TyClass::Data(_))
    )
}

fn check_spec_fn_call(name: &str, arity: usize, scope: &ExprScope) -> bool {
    let Some(facts) = scope.facts else {
        return true;
    };
    if scope.names.contains(name) || name.starts_with(GENERATED_PREFIX) {
        return false;
    }
    let Some(func) = facts.root_spec_fns.get(name) else {
        return false;
    };
    if facts.fn_count(name) != 1 || facts.item_count(name) != 1 {
        return false;
    }
    if !func.sig.generics.params.is_empty() || func.sig.inputs.len() != arity {
        return false;
    }
    for input in &func.sig.inputs {
        match input {
            syn::FnArg::Typed(pt) if spec_sig_type_ok(&pt.ty, facts) => {}
            _ => return false,
        }
    }
    match &func.sig.output {
        syn::ReturnType::Type(_, ty) => spec_sig_type_ok(ty, facts),
        syn::ReturnType::Default => false,
    }
}

fn check_stmt_admission(
    ts: &TStmt,
    scope: &mut ExprScope,
    called: &BTreeSet<String>,
) -> Result<(), String> {
    match ts {
        TStmt::Block(_, stmts) => {
            for s in stmts {
                check_stmt_admission(s, scope, called)?;
            }
            Ok(())
        }
        TStmt::Let {
            pat,
            ty,
            kind,
            refute,
            expr,
            body,
            ..
        } => {
            if *refute != Refute::Exhaustive {
                return Err("`require let` / `assert let` are not yet supported".to_string());
            }
            if *kind == LetKind::BirdsEye {
                return Err("`birds_eye` is not supported".to_string());
            }
            let Pat::Ident(pi) = pat else {
                return Err(format!(
                    "let pattern `{}` is not supported; bind a single identifier",
                    expr_text(pat)
                ));
            };
            if pi.by_ref.is_some()
                || pi.mutability.is_some()
                || pi.subpat.is_some()
                || !pi.attrs.is_empty()
            {
                return Err(format!(
                    "let pattern `{}` is not supported; bind a single identifier",
                    expr_text(pat)
                ));
            }
            if let Some(ty) = ty {
                let ok = matches!(ty.as_ref(), Type::Path(tp) if tp.qself.is_none() && (tp.path.is_ident("int") || tp.path.is_ident("bool")));
                if !ok {
                    return Err(format!(
                        "let type `{}` is not supported (only `int`/`bool` annotations)",
                        ty_string(ty)
                    ));
                }
            }
            check_binding_name(&pi.ident, called)?;
            check_expr(expr, scope)?;
            let name = pi.ident.to_string();
            let added = scope.names.insert(name.clone());
            let result = check_stmt_admission(body, scope, called);
            if added {
                scope.names.remove(&name);
            }
            result
        }
        TStmt::If { cond, thn, els, .. } => {
            check_expr(cond, scope)?;
            check_stmt_admission(thn, scope, called)?;
            check_stmt_admission(els, scope, called)
        }
        TStmt::Match { .. } => Err("`match` in a transition is not yet supported".to_string()),
        TStmt::Assert(..) => Err("`assert` in a transition is not yet supported (weak/strong relations and the safety lemma are D1b); refusing rather than dropping it".to_string()),
        TStmt::Require(_, e) | TStmt::Update(_, _, e) | TStmt::Init(_, _, e) => {
            check_expr(e, scope)
        }
        TStmt::SubUpdate(_, f, _, _) => Err(format!(
            "sub-field/index `update {f}…` is not yet supported"
        )),
        TStmt::Special { op, .. } => Err(format!(
            "sharding operation `{}` is only valid in tokenized_state_machine!",
            op.op
        )),
    }
}

fn param_refusal(p: &TransitionParam) -> String {
    format!(
        "parameter `{}` has type `{}`; only int/nat/bool and admitted datatypes are supported",
        p.name,
        ty_string(&p.ty)
    )
}

fn attr_allowed_on(attrs: &[Attribute], marker: &str, what: &str) -> Result<(), String> {
    for attr in attrs {
        if is_doc_attr(attr) {
            continue;
        }
        let is_marker = match (&attr.meta, marker) {
            (Meta::Path(p), "invariant") => p.is_ident("invariant"),
            (Meta::List(l), "inductive") => l.path.is_ident("inductive"),
            _ => false,
        };
        if !is_marker {
            return Err(format!(
                "attribute `{}` is not allowed on {what}",
                attr_text(attr)
            ));
        }
    }
    Ok(())
}

fn body_has_contract_macro(block: &syn::Block) -> bool {
    struct Finder(bool);
    impl<'ast> Visit<'ast> for Finder {
        fn visit_macro(&mut self, node: &'ast syn::Macro) {
            if let Some(last) = node.path.segments.last() {
                let name = last.ident.to_string();
                let name = name.strip_prefix("trust_vc_").unwrap_or(&name);
                if matches!(name, "requires" | "ensures" | "recommends" | "decreases") {
                    self.0 = true;
                }
            }
            syn::visit::visit_macro(self, node);
        }
    }
    let mut finder = Finder(false);
    finder.visit_block(block);
    finder.0
}

/// Names generated per machine, including the upstream-only generated names a
/// user item must not reuse.
pub(crate) fn machine_method_names(machine: &Machine) -> Vec<String> {
    let mut names = vec![
        "init".to_string(),
        "next".to_string(),
        "next_strong".to_string(),
        "invariant".to_string(),
        "init_by".to_string(),
        "next_by".to_string(),
        "next_strong_by".to_string(),
    ];
    for tr in &machine.transitions {
        let n = tr.name.to_string();
        names.push(format!("{n}_enabled"));
        if tr.kind != TransitionKind::Init {
            names.push(format!("{n}_strong"));
            names.push(format!("{n}_asserts"));
        }
    }
    names
}

#[allow(clippy::too_many_arguments)]
fn admit(
    machine: &Machine,
    attrs: &[Attribute],
    generics: Option<&syn::Generics>,
    labels: &[String],
    helper_fns: &[syn::ItemFn],
    facts: Option<&FileFacts>,
) -> Result<(), String> {
    let name = &machine.name;
    if !attrs.is_empty() {
        return Err("attributes on state_machine! are not yet supported".to_string());
    }
    if generics.is_some() {
        return Err("generic state machines are not yet supported".to_string());
    }
    if !labels.is_empty() {
        return Err("transition labels (`Label`/`InitLabel`) are not yet supported".to_string());
    }
    if let Some(helper) = helper_fns.first() {
        return Err(format!(
            "helper fn `{}` inside state_machine! is not yet supported; declare it at the file root",
            helper.sig.ident
        ));
    }
    let name_text = name.to_string();
    if name_text.starts_with(GENERATED_PREFIX) {
        return Err(format!(
            "generated item `{name_text}` collides with an existing item"
        ));
    }
    if let Some(facts) = facts {
        if let Some(existing) = facts.names_with_prefix(GENERATED_PREFIX) {
            return Err(format!(
                "generated item `{existing}` collides with an existing item"
            ));
        }
        if facts.item_count(&name_text) > 0 {
            return Err(format!(
                "machine name `{name_text}` collides with another item named `{name_text}`"
            ));
        }
        if let Some(scalar) = facts.declares_scalar_name() {
            return Err(format!(
                "this file declares an item named `{scalar}`, which would change the meaning of the D1a scalar field types"
            ));
        }
    }

    // Fields.
    let mut field_classes = BTreeMap::new();
    for field in &machine.fields {
        if field.name.to_string().starts_with(GENERATED_PREFIX) {
            return Err(format!(
                "generated item `{}` collides with an existing item",
                field.name
            ));
        }
        let class =
            classify_type(&field.ty, facts, false).map_err(|why| field_refusal(field, why))?;
        field_classes.insert(field.name.to_string(), class);
    }

    // Transitions.
    let mut item_names: BTreeSet<String> = BTreeSet::new();
    for generated in machine_method_names(machine) {
        item_names.insert(generated);
    }
    for tr in &machine.transitions {
        if tr.kind == TransitionKind::Property {
            return Err(
                "`property!` is not yet supported (it has no relation; its asserts are D1b)"
                    .to_string(),
            );
        }
        if !item_names.insert(tr.name.to_string()) {
            return Err("duplicate item name".to_string());
        }
        let mut called = BTreeSet::new();
        called_fn_names(&tr.body, &mut called);
        let mut names = BTreeSet::new();
        for p in &tr.params {
            check_binding_name(&p.name, &called)?;
            classify_type(&p.ty, facts, true).map_err(|_| param_refusal(p))?;
            names.insert(p.name.to_string());
        }
        let mut scope = ExprScope {
            kind: tr.kind,
            names,
            fields: &field_classes,
            facts,
        };
        check_stmt_admission(&tr.body, &mut scope, &called)?;
    }

    // Invariants.
    for inv in &machine.invariants {
        attr_allowed_on(
            &inv.func.attrs,
            "invariant",
            "an invariant fn (only #[invariant] and doc comments)",
        )?;
        let sig = &inv.func.sig;
        if sig.constness.is_some()
            || sig.asyncness.is_some()
            || sig.unsafety.is_some()
            || sig.abi.is_some()
        {
            return Err(format!("invariant `{}` must be a plain fn", sig.ident));
        }
        let inv_name = sig.ident.to_string();
        if inv_name.starts_with(GENERATED_PREFIX) {
            return Err(format!(
                "generated item `{inv_name}` collides with an existing item"
            ));
        }
        if !item_names.insert(inv_name) {
            return Err("duplicate item name".to_string());
        }
        if !matches!(inv.func.block.stmts.as_slice(), [syn::Stmt::Expr(_, None)]) {
            return Err(format!(
                "invariant `{}` body must be a single expression",
                sig.ident
            ));
        }
    }

    // Lemmas.
    for lemma in &machine.lemmas {
        attr_allowed_on(
            &lemma.func.attrs,
            "inductive",
            "an inductive lemma (only #[inductive(..)] and doc comments)",
        )?;
        let sig = &lemma.func.sig;
        if sig.constness.is_some()
            || sig.asyncness.is_some()
            || sig.unsafety.is_some()
            || sig.abi.is_some()
            || sig.variadic.is_some()
        {
            return Err(format!("lemma `{}` must be a plain fn", sig.ident));
        }
        if body_has_contract_macro(&lemma.func.block) {
            return Err("requires!/ensures!/recommends!/decreases! inside an inductive lemma body are not allowed; the contract is generated".to_string());
        }
        let lemma_name = sig.ident.to_string();
        if lemma_name.starts_with(GENERATED_PREFIX) {
            return Err(format!(
                "generated item `{lemma_name}` collides with an existing item"
            ));
        }
        if !item_names.insert(lemma_name.clone()) {
            return Err(format!(
                "lemma name `{lemma_name}` is not unique in this file"
            ));
        }
        if let Some(facts) = facts {
            if facts.item_count(&lemma_name) > 0 {
                return Err(format!(
                    "lemma name `{lemma_name}` is not unique in this file"
                ));
            }
        }
    }
    Ok(())
}
