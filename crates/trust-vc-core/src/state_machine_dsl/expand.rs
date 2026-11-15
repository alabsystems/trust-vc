//! File-lane and proc-macro-lane generation for admitted machines, the
//! file-wide `X::State…` path rewrite, and poison markers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::{Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};
use quote::{format_ident, quote, quote_spanned, ToTokens};
use syn::{File, Item};

use super::parse::TransitionKind;
use super::relation::compile_transition;
use super::wf::{check_machine, machine_method_names, FileFacts, LemmaKind, Machine};
use super::{
    GENERATED_MARKER, GENERATED_PREFIX, POISON_PREFIX, REFUSED_MARKER_MACRO, UNREAD_MARKER_FLAG,
};
use crate::macro_scope::{resolve_item_macro, ItemMacroResolution};

pub(crate) const MACRO_NAMES: &[&str] = &["state_machine", "tokenized_state_machine"];

pub(crate) fn is_sm_invocation(item: &Item) -> bool {
    match item {
        Item::Macro(m) if m.ident.is_none() => m
            .mac
            .path
            .segments
            .last()
            .is_some_and(|seg| MACRO_NAMES.contains(&seg.ident.to_string().as_str())),
        _ => false,
    }
}

/// True when `items` (recursively through inline modules) holds an
/// item-position `state_machine!`/`tokenized_state_machine!` invocation.
pub(crate) fn has_invocations(items: &[Item]) -> bool {
    items.iter().any(|item| match item {
        Item::Mod(m) => m
            .content
            .as_ref()
            .is_some_and(|(_, inner)| has_invocations(inner)),
        other => is_sm_invocation(other),
    })
}

/// The first identifier of an invocation's input, used to name refusals.
fn invocation_name(mac: &syn::Macro) -> String {
    let mut iter = mac.tokens.clone().into_iter();
    loop {
        match iter.next() {
            Some(TokenTree::Punct(p)) if p.as_char() == '#' => {
                let _ = iter.next();
            }
            Some(TokenTree::Ident(ident)) => return ident.to_string(),
            _ => return "?".to_string(),
        }
    }
}

fn prefix(name: &str) -> String {
    format!("state_machine! `{name}`: ")
}

fn span_line(span: Span) -> usize {
    span.start().line.max(1)
}

/// Poison registry: every entry becomes a root marker item.
#[derive(Default)]
struct PoisonTable {
    entries: Vec<(usize, String)>,
}

impl PoisonTable {
    fn add(&mut self, line: usize, msg: String) -> usize {
        self.entries.push((line, msg));
        self.entries.len() - 1
    }

    fn ident(k: usize, span: Span) -> Ident {
        Ident::new(&format!("{POISON_PREFIX}{k}"), span)
    }

    /// A marker item; `unread` marks one that stands for items the lane does
    /// not read (see [`UNREAD_MARKER_FLAG`]).
    fn marker(k: usize, line: usize, msg: &str, unread: bool) -> Item {
        let mac = Ident::new(REFUSED_MARKER_MACRO, Span::call_site());
        let k_lit = proc_macro2::Literal::usize_unsuffixed(k);
        let line_lit = proc_macro2::Literal::usize_unsuffixed(line);
        let msg_lit = proc_macro2::Literal::string(msg);
        let flag = unread.then(|| Ident::new(UNREAD_MARKER_FLAG, Span::call_site()));
        syn::parse2(quote!(#mac! { #k_lit #line_lit #msg_lit #flag }))
            .expect("marker item is well-formed")
    }
}

/// What the rewriter knows about each machine name.
struct AdmittedNames {
    relations: BTreeSet<String>,
    lemmas: BTreeSet<String>,
    invariants: BTreeSet<String>,
}

struct RewriteCtx<'a> {
    admitted: &'a BTreeMap<String, AdmittedNames>,
    /// Refused machine name -> refusal message.
    refused: &'a BTreeMap<String, String>,
    /// Bare names imported from a machine module -> machine name.
    imported: &'a BTreeMap<String, String>,
}

struct Rewriter<'a, 'b> {
    ctx: &'b RewriteCtx<'a>,
    poison: &'b mut PoisonTable,
    depth: usize,
    changed: bool,
}

fn is_sep(trees: &[TokenTree], i: usize) -> bool {
    matches!(
        (trees.get(i), trees.get(i + 1)),
        (Some(TokenTree::Punct(a)), Some(TokenTree::Punct(b)))
            if a.as_char() == ':' && a.spacing() == Spacing::Joint && b.as_char() == ':'
    )
}

fn ident_at(trees: &[TokenTree], i: usize) -> Option<&Ident> {
    match trees.get(i) {
        Some(TokenTree::Ident(ident)) => Some(ident),
        _ => None,
    }
}

fn sep_tokens(span: Span) -> [TokenTree; 2] {
    let mut a = Punct::new(':', Spacing::Joint);
    a.set_span(span);
    let mut b = Punct::new(':', Spacing::Alone);
    b.set_span(span);
    [TokenTree::Punct(a), TokenTree::Punct(b)]
}

impl Rewriter<'_, '_> {
    fn poison(&mut self, span: Span, machine: &str, msg: &str) -> Vec<TokenTree> {
        let k = self
            .poison
            .add(span_line(span), format!("{}{msg}", prefix(machine)));
        self.changed = true;
        vec![TokenTree::Ident(PoisonTable::ident(k, span))]
    }

    /// Generated items are file-root items, and a reference to one is only
    /// ever rewritten at depth 0 (see `try_path`), so the replacement is the
    /// bare generated ident.
    fn root_ref(&self, ident: Ident) -> Vec<TokenTree> {
        vec![TokenTree::Ident(ident)]
    }

    fn stream(&mut self, ts: TokenStream) -> TokenStream {
        let trees: Vec<TokenTree> = ts.into_iter().collect();
        let mut out: Vec<TokenTree> = Vec::with_capacity(trees.len());
        let mut i = 0;
        while i < trees.len() {
            match &trees[i] {
                TokenTree::Group(g) => {
                    let inner = self.stream(g.stream());
                    let mut ng = Group::new(g.delimiter(), inner);
                    ng.set_span(g.span());
                    out.push(TokenTree::Group(ng));
                    i += 1;
                }
                TokenTree::Ident(_) => {
                    if let Some((consumed, replacement)) = self.try_path(&trees, i) {
                        out.extend(replacement);
                        i += consumed;
                    } else {
                        out.push(trees[i].clone());
                        i += 1;
                    }
                }
                other => {
                    out.push(other.clone());
                    i += 1;
                }
            }
        }
        out.into_iter().collect()
    }

    fn try_path(&mut self, trees: &[TokenTree], i: usize) -> Option<(usize, Vec<TokenTree>)> {
        let prev_sep = i >= 2 && is_sep(trees, i - 2);
        let prev_dot = matches!(trees.get(i.wrapping_sub(1)), Some(TokenTree::Punct(p)) if i > 0 && p.as_char() == '.');
        // `::X` with nothing path-like before the separator is a leading `::`.
        let leading_colon = prev_sep
            && !matches!(trees.get(i.wrapping_sub(3)), Some(TokenTree::Ident(_)) if i >= 3)
            && !matches!(trees.get(i.wrapping_sub(3)), Some(TokenTree::Punct(p)) if i >= 3 && p.as_char() == '>');
        let mut j = i;
        let mut prefix_segs: Vec<String> = Vec::new();
        while let Some(ident) = ident_at(trees, j) {
            let text = ident.to_string();
            if matches!(text.as_str(), "crate" | "self" | "super") && is_sep(trees, j + 1) {
                prefix_segs.push(text);
                j += 3;
            } else {
                break;
            }
        }
        let root = ident_at(trees, j)?.clone();
        let root_text = root.to_string();

        // Bare imported names.
        if j == i && !prev_sep && !prev_dot {
            if let Some(machine) = self.ctx.imported.get(&root_text) {
                if !is_sep(trees, j + 1) {
                    let machine = machine.clone();
                    let msg = format!("importing from state machine module `{machine}` is not supported; write `{machine}::State`");
                    return Some((1, self.poison(root.span(), &machine, &msg)));
                }
            }
        }

        if !is_sep(trees, j + 1) {
            return None;
        }
        let is_admitted = self.ctx.admitted.contains_key(&root_text);
        let refused_msg = self.ctx.refused.get(&root_text).cloned();
        if !is_admitted && refused_msg.is_none() {
            return None;
        }
        // Collect the segments after `X ::`.
        let mut segs: Vec<String> = Vec::new();
        let mut k = j + 3;
        let mut generic = false;
        loop {
            match ident_at(trees, k) {
                Some(ident) => {
                    segs.push(ident.to_string());
                    k += 1;
                    if is_sep(trees, k) {
                        if ident_at(trees, k + 2).is_some() {
                            k += 2;
                            continue;
                        }
                        generic = true;
                        k += 2;
                    }
                    break;
                }
                None => {
                    generic = true;
                    break;
                }
            }
        }
        let consumed = k - i;
        let span = root.span();
        if let Some(msg) = refused_msg {
            // Refused: every `X::…` spelling is poisoned, whatever precedes it.
            return Some((consumed, self.poison(span, &root_text, &msg)));
        }
        if prev_dot {
            return None;
        }
        let prev_use = i >= 1 && matches!(&trees[i - 1], TokenTree::Ident(kw) if kw == "use");
        if prev_use {
            let msg = format!("importing from state machine module `{root_text}` is not supported; write `{root_text}::State`");
            return Some((consumed, self.poison(span, &root_text, &msg)));
        }
        if prev_sep && !leading_colon {
            // `m::X::…` names something other than the root machine.
            return None;
        }
        let full = format!("{root_text}::{}", segs.join("::"));
        let not_generated = format!("`{full}` is not generated by D1a state_machine!");
        if leading_colon || generic {
            return Some((consumed, self.poison(span, &root_text, &not_generated)));
        }
        let prefix_ok = match prefix_segs.as_slice() {
            [] => true,
            [only] if only == "crate" => true,
            [only] if only == "self" => self.depth == 0,
            supers => supers.len() == self.depth && supers.iter().all(|s| s == "super"),
        };
        if !prefix_ok {
            return Some((consumed, self.poison(span, &root_text, &not_generated)));
        }
        if self.depth > 0 {
            // The generated items live at the FILE ROOT; a reference from
            // inside an inline module would resolve through a `crate::` path
            // the engine's bare-name registries do not model, so it is refused
            // rather than left to fail with a type-inference error.
            let msg = format!(
                "referencing `{root_text}::…` from inside an inline module is not supported in D1a; write the client at the file root"
            );
            return Some((consumed, self.poison(span, &root_text, &msg)));
        }
        let names = &self.ctx.admitted[&root_text];
        let replacement = match segs.as_slice() {
            [state] if state == "State" => {
                let ident = Ident::new(&format!("{GENERATED_PREFIX}{root_text}_State"), span);
                self.root_ref(ident)
            }
            [state, g] if state == "State" && names.relations.contains(g) => {
                let ident = Ident::new(&format!("{GENERATED_PREFIX}{root_text}__{g}"), span);
                self.root_ref(ident)
            }
            [state, l] if state == "State" && names.lemmas.contains(l) => {
                let ident = Ident::new(l, span);
                self.root_ref(ident)
            }
            [state, inv] if state == "State" && names.invariants.contains(inv) => {
                let msg = format!("call `.{inv}()` with method syntax");
                return Some((consumed, self.poison(span, &root_text, &msg)));
            }
            _ => return Some((consumed, self.poison(span, &root_text, &not_generated))),
        };
        self.changed = true;
        Some((consumed, replacement))
    }
}

/// `Self`/`State` at a path start inside machine-internal code -> `X::State`.
fn internal_self_rewrite(ts: TokenStream, machine: &Ident) -> TokenStream {
    let trees: Vec<TokenTree> = ts.into_iter().collect();
    let mut out = Vec::with_capacity(trees.len());
    for (i, tree) in trees.iter().enumerate() {
        match tree {
            TokenTree::Group(g) => {
                let mut ng = Group::new(g.delimiter(), internal_self_rewrite(g.stream(), machine));
                ng.set_span(g.span());
                out.push(TokenTree::Group(ng));
            }
            TokenTree::Ident(ident) if ident == "Self" || ident == "State" => {
                let prev_sep = i >= 2 && is_sep(&trees, i - 2);
                let prev_dot =
                    i >= 1 && matches!(&trees[i - 1], TokenTree::Punct(p) if p.as_char() == '.');
                if prev_sep || prev_dot {
                    out.push(tree.clone());
                } else {
                    let span = ident.span();
                    out.push(TokenTree::Ident(Ident::new(&machine.to_string(), span)));
                    out.extend(sep_tokens(span));
                    out.push(TokenTree::Ident(Ident::new("State", span)));
                }
            }
            other => out.push(other.clone()),
        }
    }
    out.into_iter().collect()
}

fn join_tokens(parts: &[TokenStream], sep: TokenStream) -> Option<TokenStream> {
    let mut iter = parts.iter();
    let first = iter.next()?;
    let mut acc = first.clone();
    for part in iter {
        acc = quote!(#acc #sep #part);
    }
    Some(acc)
}

fn marker_attr() -> TokenStream {
    quote!(#[doc = #GENERATED_MARKER])
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Lane {
    File,
    ProcMacro,
}

/// Generate the items of one admitted machine. `rewrite` is applied to
/// machine-internal user code (after the `Self`/`State` rewrite).
fn generate(
    machine: &Machine,
    lane: Lane,
    rewrite: &mut dyn FnMut(TokenStream) -> TokenStream,
) -> Result<Vec<TokenStream>, String> {
    let name = &machine.name;
    let name_text = name.to_string();
    let span = name.span();
    let marker = marker_attr();
    let state = Ident::new(&format!("{GENERATED_PREFIX}{name_text}_State"), span);
    let rel =
        |t: &str, span: Span| Ident::new(&format!("{GENERATED_PREFIX}{name_text}__{t}"), span);
    let mut items = Vec::new();

    // Struct.
    let field_decls: Vec<TokenStream> = machine
        .fields
        .iter()
        .map(|f| {
            let n = &f.name;
            let t = &f.ty;
            quote!(pub #n: #t)
        })
        .collect();
    let (derive, allow_unused) = match lane {
        Lane::File => (quote!(), quote!()),
        Lane::ProcMacro => (
            quote!(#[derive(Clone, Copy)] #[allow(non_camel_case_types)]),
            quote!(#[allow(unused_variables, non_snake_case, dead_code, unused_braces)]),
        ),
    };
    items.push(quote_spanned! {span=>
        #marker
        #derive
        pub struct #state { #(#field_decls,)* }
    });

    // Invariants.
    let mut inv_methods = Vec::new();
    let mut inv_bodies = Vec::new();
    for inv in &machine.invariants {
        let syn::Stmt::Expr(body, None) = &inv.func.block.stmts[0] else {
            return Err("internal: invariant body shape".to_string());
        };
        let body_tokens = rewrite(internal_self_rewrite(body.to_token_stream(), name));
        let ident = &inv.func.sig.ident;
        let docs: Vec<&syn::Attribute> = inv
            .func
            .attrs
            .iter()
            .filter(|a| a.path().is_ident("doc"))
            .collect();
        inv_methods.push(quote! {
            #(#docs)*
            #marker
            #[trust_vc::spec]
            #allow_unused
            pub fn #ident(&self) -> bool { #body_tokens }
        });
        inv_bodies.push(quote!((#body_tokens)));
    }
    let inv_conj = join_tokens(&inv_bodies, quote!(&&)).unwrap_or_else(|| quote!(true));
    let invariant_ident = Ident::new("invariant", span);
    items.push(quote_spanned! {span=>
        impl #state {
            #(#inv_methods)*
            #marker
            #[trust_vc::spec]
            #allow_unused
            pub fn #invariant_ident(&self) -> bool { #inv_conj }
        }
    });

    let exists_path = match lane {
        Lane::File => quote!(exists),
        Lane::ProcMacro => quote!(::trust_vc::exists!),
    };
    let pre = Ident::new("pre", span);
    let post = Ident::new("post", span);
    let mut init_disjuncts = Vec::new();
    let mut next_disjuncts = Vec::new();
    let mut next_strong_disjuncts = Vec::new();
    for tr in &machine.transitions {
        let tspan = tr.name.span();
        let compiled = compile_transition(tr, &machine.fields, &pre, &post)?;
        let relation = &compiled.relation;
        let enabled = &compiled.enabled;
        let params: Vec<TokenStream> = tr
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let t = &p.ty;
                quote!(#n: #t)
            })
            .collect();
        let args: Vec<&Ident> = tr.params.iter().map(|p| &p.name).collect();
        let t = tr.name.to_string();
        let main = rel(&t, tspan);
        let enabled_ident = rel(&format!("{t}_enabled"), tspan);
        let wrap = |call: TokenStream| -> TokenStream {
            if params.is_empty() {
                call
            } else {
                quote!(#exists_path(|#(#params),*| #call))
            }
        };
        match tr.kind {
            TransitionKind::Init => {
                items.push(quote! {
                    #marker
                    #[trust_vc::spec]
                    #allow_unused
                    pub fn #main(#post: #state #(, #params)*) -> bool { #relation }
                });
                items.push(quote! {
                    #marker
                    #[trust_vc::spec]
                    #allow_unused
                    pub fn #enabled_ident(#(#params),*) -> bool { #enabled }
                });
                init_disjuncts.push(wrap(quote!(#main(#post #(, #args)*))));
            }
            TransitionKind::Transition | TransitionKind::Readonly => {
                let strong = rel(&format!("{t}_strong"), tspan);
                items.push(quote! {
                    #marker
                    #[trust_vc::spec]
                    #allow_unused
                    pub fn #main(#pre: #state, #post: #state #(, #params)*) -> bool { #relation }
                });
                items.push(quote! {
                    #marker
                    #[trust_vc::spec]
                    #allow_unused
                    pub fn #strong(#pre: #state, #post: #state #(, #params)*) -> bool { #relation }
                });
                items.push(quote! {
                    #marker
                    #[trust_vc::spec]
                    #allow_unused
                    pub fn #enabled_ident(#pre: #state #(, #params)*) -> bool { #enabled }
                });
                next_disjuncts.push(wrap(quote!(#main(#pre, #post #(, #args)*))));
                next_strong_disjuncts.push(wrap(quote!(#strong(#pre, #post #(, #args)*))));
            }
            TransitionKind::Property => {
                return Err("internal: property reached generation".to_string());
            }
        }
    }
    let disj = |parts: &[TokenStream]| -> TokenStream {
        let wrapped: Vec<TokenStream> = parts.iter().map(|p| quote!((#p))).collect();
        join_tokens(&wrapped, quote!(||)).unwrap_or_else(|| quote!(false))
    };
    let init_body = disj(&init_disjuncts);
    let next_body = disj(&next_disjuncts);
    let next_strong_body = disj(&next_strong_disjuncts);
    let init_ident = rel("init", span);
    let next_ident = rel("next", span);
    let next_strong_ident = rel("next_strong", span);
    items.push(quote! {
        #marker
        #[trust_vc::spec]
        #allow_unused
        pub fn #init_ident(#post: #state) -> bool { #init_body }
    });
    items.push(quote! {
        #marker
        #[trust_vc::spec]
        #allow_unused
        pub fn #next_ident(#pre: #state, #post: #state) -> bool { #next_body }
    });
    items.push(quote! {
        #marker
        #[trust_vc::spec]
        #allow_unused
        pub fn #next_strong_ident(#pre: #state, #post: #state) -> bool { #next_strong_body }
    });

    // Lemmas.
    for lemma in &machine.lemmas {
        let tr = machine
            .transitions
            .iter()
            .find(|t| t.name == lemma.target)
            .ok_or_else(|| "internal: lemma target".to_string())?;
        let args: Vec<&Ident> = tr.params.iter().map(|p| &p.name).collect();
        let t = tr.name.to_string();
        let requires = match lemma.kind {
            LemmaKind::Init => {
                let main = rel(&t, tr.name.span());
                quote!(#main(#post #(, #args)*))
            }
            LemmaKind::Transition => {
                let strong = rel(&format!("{t}_strong"), tr.name.span());
                quote!(#pre.invariant() && #strong(#pre, #post #(, #args)*))
            }
        };
        let ensures = quote!(#post.invariant());
        let func = &lemma.func;
        let docs: Vec<&syn::Attribute> = func
            .attrs
            .iter()
            .filter(|a| a.path().is_ident("doc"))
            .collect();
        let ident = &func.sig.ident;
        let inputs = rewrite(internal_self_rewrite(
            func.sig.inputs.to_token_stream(),
            name,
        ));
        let block = rewrite(internal_self_rewrite(func.block.to_token_stream(), name));
        let contract = match lane {
            Lane::File => quote! {
                #[trust_vc::requires(#requires)]
                #[trust_vc::ensures(#ensures)]
            },
            // The compile lane spells the same contract through
            // `#[trust_vc::contract(..)]`, the only attribute form the proc-macro
            // surface has; `returns(..)` names the (unit) result, which
            // `contract` requires whenever `ensures` is present.
            Lane::ProcMacro => quote! {
                #[trust_vc::contract(
                    requires(#requires),
                    ensures(#ensures),
                    returns(__trust_vc_sm_unit)
                )]
            },
        };
        items.push(quote! {
            #(#docs)*
            #marker
            #[trust_vc::proof]
            #contract
            #allow_unused
            pub fn #ident(#inputs) #block
        });
    }
    Ok(items)
}

fn parse_items(tokens: Vec<TokenStream>) -> Result<Vec<Item>, String> {
    tokens
        .into_iter()
        .map(|ts| {
            syn::parse2::<Item>(ts)
                .map_err(|e| format!("internal: generated item failed to parse: {e}"))
        })
        .collect()
}

/// Names a use tree binds when its root (after `crate`/`self`/`super`) is one
/// of `machines`: returns (machine, bound names; `None` for a glob).
fn use_imports_from(
    tree: &syn::UseTree,
    machines: &BTreeSet<String>,
) -> Vec<(String, Vec<String>)> {
    fn leaves(tree: &syn::UseTree, out: &mut Vec<String>) {
        match tree {
            syn::UseTree::Path(p) => leaves(&p.tree, out),
            syn::UseTree::Name(n) => out.push(n.ident.to_string()),
            syn::UseTree::Rename(r) => out.push(r.rename.to_string()),
            syn::UseTree::Glob(_) => {
                for name in [
                    "State",
                    "Step",
                    "Config",
                    "show",
                    "take_step",
                    "Label",
                    "InitLabel",
                ] {
                    out.push(name.to_string());
                }
            }
            syn::UseTree::Group(g) => {
                for item in &g.items {
                    leaves(item, out);
                }
            }
        }
    }
    let mut found = Vec::new();
    match tree {
        syn::UseTree::Path(p) => {
            let root = p.ident.to_string();
            if matches!(root.as_str(), "crate" | "self" | "super") {
                found.extend(use_imports_from(&p.tree, machines));
            } else if machines.contains(&root) {
                let mut names = Vec::new();
                leaves(&p.tree, &mut names);
                found.push((root, names));
            }
        }
        syn::UseTree::Group(g) => {
            for item in &g.items {
                found.extend(use_imports_from(item, machines));
            }
        }
        syn::UseTree::Name(n) if machines.contains(&n.ident.to_string()) => {
            found.push((n.ident.to_string(), Vec::new()));
        }
        syn::UseTree::Rename(r) if machines.contains(&r.ident.to_string()) => {
            found.push((r.ident.to_string(), vec![r.rename.to_string()]));
        }
        _ => {}
    }
    found
}

enum RootOutcome {
    Admitted(Box<Machine>),
    Refused(String, String),
    Untouched,
}

/// Replace every nested (non-root) invocation with a marker; returns the
/// machine names so references can be poisoned.
fn poison_nested(
    file: &File,
    items: &mut [Item],
    path: &mut Vec<usize>,
    poison: &mut PoisonTable,
    refused: &mut BTreeMap<String, String>,
) {
    for (index, item) in items.iter_mut().enumerate() {
        path.push(index);
        match item {
            Item::Mod(module) => {
                if let Some((_, inner)) = &mut module.content {
                    poison_nested(file, inner, path, poison, refused);
                }
            }
            Item::Macro(m) if path.len() > 1 && is_sm_invocation(&Item::Macro(m.clone())) => {
                let resolution = resolve_item_macro(file, path);
                if resolution != ItemMacroResolution::LocalMacroRules {
                    let name = invocation_name(&m.mac);
                    let msg = if m
                        .mac
                        .path
                        .segments
                        .last()
                        .is_some_and(|s| s.ident == "tokenized_state_machine")
                    {
                        "tokenized_state_machine! is not yet supported".to_string()
                    } else {
                        "state_machine! is only supported at the file root in D1a".to_string()
                    };
                    let full = format!("{}{msg}", prefix(&name));
                    let k = poison.add(span_line(m.mac.path.span_start()), full.clone());
                    refused.entry(name).or_insert(full);
                    *item = PoisonTable::marker(
                        k,
                        span_line(m.mac.path.span_start()),
                        &poison.entries[k].1,
                        resolution == ItemMacroResolution::Other,
                    );
                    // The marker is emitted in place; do not duplicate it at root.
                    poison.entries[k].0 = usize::MAX;
                }
            }
            _ => {}
        }
        path.pop();
    }
}

trait SpanStart {
    fn span_start(&self) -> Span;
}

impl SpanStart for syn::Path {
    fn span_start(&self) -> Span {
        self.segments
            .first()
            .map(|s| s.ident.span())
            .unwrap_or_else(Span::call_site)
    }
}

fn root_invocation_message(m: &syn::ItemMacro, resolution: ItemMacroResolution) -> Option<String> {
    let is_tokenized = m
        .mac
        .path
        .segments
        .last()
        .is_some_and(|s| s.ident == "tokenized_state_machine");
    match resolution {
        ItemMacroResolution::LocalMacroRules => None,
        ItemMacroResolution::TrustVc if is_tokenized => {
            Some("tokenized_state_machine! is not yet supported".to_string())
        }
        ItemMacroResolution::TrustVc => Some(String::new()),
        ItemMacroResolution::Other if is_tokenized => {
            Some("tokenized_state_machine! is not yet supported".to_string())
        }
        ItemMacroResolution::Other => {
            if m.mac.path.segments.len() == 1 && m.mac.path.leading_colon.is_none() {
                Some("bare state_machine! is not resolved to trust_vc here; write `trust_vc::state_machine!`".to_string())
            } else {
                let path = m
                    .mac
                    .path
                    .segments
                    .iter()
                    .map(|s| s.ident.to_string())
                    .collect::<Vec<_>>()
                    .join("::");
                Some(format!(
                    "state_machine! via `{path}` is not trust_vc's macro and is not verified"
                ))
            }
        }
    }
}

/// File-lane expansion. See the module docs in `mod.rs`.
pub(crate) fn expand_file(file: &mut File) {
    if !has_invocations(&file.items) {
        return;
    }
    let original = file.clone();
    let facts = FileFacts::collect(&original.items);
    let mut poison = PoisonTable::default();
    let mut refused: BTreeMap<String, String> = BTreeMap::new();

    // Root invocations.
    let mut outcomes: Vec<(usize, RootOutcome, usize)> = Vec::new();
    // Root invocations that do not resolve to trust_vc's macro: whatever they
    // expand to is not read.
    let mut foreign_roots: BTreeSet<usize> = BTreeSet::new();
    for (index, item) in original.items.iter().enumerate() {
        let Item::Macro(m) = item else { continue };
        if !is_sm_invocation(item) {
            continue;
        }
        let line = span_line(m.mac.path.span_start());
        let resolution = resolve_item_macro(&original, &[index]);
        if resolution == ItemMacroResolution::Other {
            foreign_roots.insert(index);
        }
        let name = invocation_name(&m.mac);
        match root_invocation_message(m, resolution) {
            None => outcomes.push((index, RootOutcome::Untouched, line)),
            Some(msg) if !msg.is_empty() => {
                outcomes.push((index, RootOutcome::Refused(name, msg), line))
            }
            Some(_) => match check_machine(m.mac.tokens.clone(), Some(&facts)) {
                Ok(machine) => {
                    outcomes.push((index, RootOutcome::Admitted(Box::new(machine)), line))
                }
                Err(errors) => {
                    outcomes.push((index, RootOutcome::Refused(name, errors.join("; ")), line))
                }
            },
        }
    }

    // Cross-machine checks: duplicate machine names, generated/lemma names.
    let mut seen_names: BTreeMap<String, usize> = BTreeMap::new();
    let mut generated_names: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (pos, (_, outcome, _)) in outcomes.iter().enumerate() {
        let name = match outcome {
            RootOutcome::Admitted(m) => m.name.to_string(),
            RootOutcome::Refused(n, _) => n.clone(),
            RootOutcome::Untouched => continue,
        };
        *seen_names.entry(name.clone()).or_default() += 1;
        if let RootOutcome::Admitted(m) = outcome {
            let mut names = vec![format!("{GENERATED_PREFIX}{name}_State")];
            for tr in &m.transitions {
                let t = tr.name.to_string();
                names.push(format!("{GENERATED_PREFIX}{name}__{t}"));
            }
            for generated in machine_method_names(m) {
                names.push(format!("{GENERATED_PREFIX}{name}__{generated}"));
            }
            for lemma in &m.lemmas {
                names.push(lemma.func.sig.ident.to_string());
            }
            for n in names {
                generated_names.entry(n).or_default().push(pos);
            }
        }
    }
    let mut demote: BTreeMap<usize, String> = BTreeMap::new();
    for (name, positions) in &generated_names {
        let unique: BTreeSet<usize> = positions.iter().copied().collect();
        if unique.len() > 1 {
            for pos in unique {
                let msg = if name.starts_with(GENERATED_PREFIX) {
                    format!("generated item `{name}` collides with an existing item")
                } else {
                    format!("lemma name `{name}` is not unique in this file")
                };
                demote.entry(pos).or_insert(msg);
            }
        }
    }
    for (pos, (_, outcome, _)) in outcomes.iter().enumerate() {
        let name = match outcome {
            RootOutcome::Admitted(m) => m.name.to_string(),
            RootOutcome::Refused(n, _) => n.clone(),
            RootOutcome::Untouched => continue,
        };
        if seen_names.get(&name).copied().unwrap_or(0) > 1 {
            demote.entry(pos).or_insert(format!(
                "machine name `{name}` collides with another item named `{name}`"
            ));
        }
    }
    // Imports from a machine module.
    let machine_names: BTreeSet<String> = seen_names.keys().cloned().collect();
    let mut imported: BTreeMap<String, String> = BTreeMap::new();
    let mut import_refusals: BTreeSet<String> = BTreeSet::new();
    fn collect_uses(
        items: &[Item],
        machines: &BTreeSet<String>,
        imported: &mut BTreeMap<String, String>,
        refusals: &mut BTreeSet<String>,
    ) {
        for item in items {
            match item {
                Item::Use(u) => {
                    for (machine, names) in use_imports_from(&u.tree, machines) {
                        refusals.insert(machine.clone());
                        for n in names {
                            imported.insert(n, machine.clone());
                        }
                    }
                }
                Item::Mod(m) => {
                    if let Some((_, inner)) = &m.content {
                        collect_uses(inner, machines, imported, refusals);
                    }
                }
                _ => {}
            }
        }
    }
    collect_uses(
        &original.items,
        &machine_names,
        &mut imported,
        &mut import_refusals,
    );
    for (pos, (_, outcome, _)) in outcomes.iter_mut().enumerate() {
        if let Some(msg) = demote.remove(&pos) {
            let name = match outcome {
                RootOutcome::Admitted(m) => m.name.to_string(),
                RootOutcome::Refused(n, _) => n.clone(),
                RootOutcome::Untouched => continue,
            };
            *outcome = RootOutcome::Refused(name, msg);
        }
        if let RootOutcome::Admitted(m) = outcome {
            let name = m.name.to_string();
            if import_refusals.contains(&name) {
                let msg = format!("importing from state machine module `{name}` is not supported; write `{name}::State`");
                *outcome = RootOutcome::Refused(name, msg);
            }
        }
    }

    // Generation dry run: an internal generation failure refuses the machine
    // BEFORE any reference to it is rewritten as if it were admitted.
    for (_, outcome, _) in outcomes.iter_mut() {
        if let RootOutcome::Admitted(m) = outcome {
            let mut identity = |ts: TokenStream| ts;
            if let Err(msg) = generate(m, Lane::File, &mut identity).and_then(parse_items) {
                let name = m.name.to_string();
                *outcome = RootOutcome::Refused(name, msg);
            }
        }
    }

    // Rewrite context.
    let mut admitted: BTreeMap<String, AdmittedNames> = BTreeMap::new();
    for (_, outcome, _) in &outcomes {
        match outcome {
            RootOutcome::Admitted(m) => {
                let mut relations = BTreeSet::new();
                relations.insert("init".to_string());
                relations.insert("next".to_string());
                relations.insert("next_strong".to_string());
                for tr in &m.transitions {
                    let t = tr.name.to_string();
                    relations.insert(t.clone());
                    relations.insert(format!("{t}_enabled"));
                    if tr.kind != TransitionKind::Init {
                        relations.insert(format!("{t}_strong"));
                    }
                }
                let mut invariants: BTreeSet<String> = m
                    .invariants
                    .iter()
                    .map(|i| i.func.sig.ident.to_string())
                    .collect();
                invariants.insert("invariant".to_string());
                admitted.insert(
                    m.name.to_string(),
                    AdmittedNames {
                        relations,
                        lemmas: m
                            .lemmas
                            .iter()
                            .map(|l| l.func.sig.ident.to_string())
                            .collect(),
                        invariants,
                    },
                );
            }
            RootOutcome::Refused(name, msg) => {
                refused
                    .entry(name.clone())
                    .or_insert_with(|| format!("{}{msg}", prefix(name)));
            }
            RootOutcome::Untouched => {}
        }
    }

    // Nested invocations (modules) are poisoned in place.
    let mut items = original.items.clone();
    poison_nested(
        &original,
        &mut items,
        &mut Vec::new(),
        &mut poison,
        &mut refused,
    );
    // `refused` messages are already prefixed; the rewriter prefixes again, so
    // strip for it.
    let refused_plain: BTreeMap<String, String> = refused
        .iter()
        .map(|(n, m)| {
            let p = prefix(n);
            (n.clone(), m.strip_prefix(&p).unwrap_or(m).to_string())
        })
        .collect();
    let ctx = RewriteCtx {
        admitted: &admitted,
        refused: &refused_plain,
        imported: &imported,
    };

    // Generate admitted machines.
    let mut generated: BTreeMap<usize, Vec<Item>> = BTreeMap::new();
    let mut refused_now: Vec<(usize, String, String, usize)> = Vec::new();
    for (index, outcome, line) in &outcomes {
        match outcome {
            RootOutcome::Admitted(machine) => {
                let mut rewrite = |ts: TokenStream| -> TokenStream {
                    let mut rw = Rewriter {
                        ctx: &ctx,
                        poison: &mut poison,
                        depth: 0,
                        changed: false,
                    };
                    rw.stream(ts)
                };
                match generate(machine, Lane::File, &mut rewrite).and_then(parse_items) {
                    Ok(machine_items) => {
                        generated.insert(*index, machine_items);
                    }
                    Err(msg) => {
                        refused_now.push((*index, machine.name.to_string(), msg, *line));
                    }
                }
            }
            RootOutcome::Refused(name, msg) => {
                refused_now.push((*index, name.clone(), msg.clone(), *line));
            }
            RootOutcome::Untouched => {}
        }
    }
    let mut root_markers: BTreeMap<usize, Item> = BTreeMap::new();
    for (index, name, msg, line) in refused_now {
        let full = format!("{}{msg}", prefix(&name));
        let k = poison.add(line, full.clone());
        poison.entries[k].0 = usize::MAX;
        root_markers.insert(
            index,
            PoisonTable::marker(k, line, &full, foreign_roots.contains(&index)),
        );
    }

    // Rewrite every other item.
    fn rewrite_items(
        items: Vec<Item>,
        ctx: &RewriteCtx,
        poison: &mut PoisonTable,
        depth: usize,
        machines: &BTreeSet<String>,
    ) -> Vec<Item> {
        let mut out = Vec::with_capacity(items.len());
        for item in items {
            match item {
                Item::Mod(mut module) => {
                    if let Some((brace, inner)) = module.content.take() {
                        module.content = Some((
                            brace,
                            rewrite_items(inner, ctx, poison, depth + 1, machines),
                        ));
                    }
                    out.push(Item::Mod(module));
                }
                Item::Macro(ref m)
                    if m.ident.is_none() && m.mac.path.is_ident(REFUSED_MARKER_MACRO) =>
                {
                    out.push(item)
                }
                Item::Use(ref u) if !use_imports_from(&u.tree, machines).is_empty() => {
                    // The import itself is dropped; every bare use of an
                    // imported name is poisoned by the rewriter.
                }
                other => {
                    let tokens = other.to_token_stream();
                    let mut rw = Rewriter {
                        ctx,
                        poison,
                        depth,
                        changed: false,
                    };
                    let rewritten = rw.stream(tokens);
                    if rw.changed {
                        match syn::parse2::<Item>(rewritten) {
                            Ok(parsed) => out.push(parsed),
                            // Unparseable after rewrite: the item is replaced
                            // by a refusal marker (the CLI reports it
                            // unscannable; a lookup by name fails closed).
                            Err(_) => {
                                let line = span_line(syn::spanned::Spanned::span(&other));
                                let msg = format!(
                                    "{}an item that mentions a state machine could not be re-parsed after path rewriting",
                                    prefix("?")
                                );
                                let k = poison.add(line, msg.clone());
                                poison.entries[k].0 = usize::MAX;
                                out.push(PoisonTable::marker(k, line, &msg, true));
                            }
                        }
                    } else {
                        out.push(other);
                    }
                }
            }
        }
        out
    }

    let mut final_items: Vec<Item> = Vec::new();
    let mut others: Vec<(usize, Item)> = Vec::new();
    for (index, item) in items.into_iter().enumerate() {
        if generated.contains_key(&index) || root_markers.contains_key(&index) {
            continue;
        }
        others.push((index, item));
    }
    let other_indices: Vec<usize> = others.iter().map(|(i, _)| *i).collect();
    let rewritten = rewrite_items(
        others.into_iter().map(|(_, item)| item).collect(),
        &ctx,
        &mut poison,
        0,
        &machine_names,
    );
    let mut rewritten_by_index: BTreeMap<usize, Item> =
        other_indices.into_iter().zip(rewritten).collect();
    let total = original.items.len();
    for index in 0..total {
        if let Some(machine_items) = generated.remove(&index) {
            final_items.extend(machine_items);
        } else if let Some(marker) = root_markers.remove(&index) {
            final_items.push(marker);
        } else if let Some(item) = rewritten_by_index.remove(&index) {
            final_items.push(item);
        }
    }
    for (k, (line, msg)) in poison.entries.iter().enumerate() {
        if *line != usize::MAX {
            final_items.push(PoisonTable::marker(k, *line, msg, false));
        }
    }
    file.items = final_items;
}

/// Proc-macro lane: the same parse/wf/admission and generation, plus the
/// compile-only shims that make `X::State::…` paths resolve under rustc.
pub(crate) fn expand_tokens(input: TokenStream) -> TokenStream {
    let name = {
        let mac: syn::Macro = syn::Macro {
            path: syn::parse_quote!(state_machine),
            bang_token: Default::default(),
            delimiter: syn::MacroDelimiter::Brace(Default::default()),
            tokens: input.clone(),
        };
        invocation_name(&mac)
    };
    let machine = match check_machine(input, None) {
        Ok(machine) => machine,
        Err(errors) => {
            let msg = format!("{}{}", prefix(&name), errors.join("; "));
            return quote!(::core::compile_error!(#msg););
        }
    };
    let mut identity = |ts: TokenStream| -> TokenStream {
        // `X::State` inside machine-internal code resolves through the shim
        // module; only `Self`/`State` need rewriting, which `generate` does.
        ts
    };
    let items = match generate(&machine, Lane::ProcMacro, &mut identity) {
        Ok(items) => items,
        Err(msg) => {
            let msg = format!("{}{msg}", prefix(&name));
            return quote!(::core::compile_error!(#msg););
        }
    };
    let shims = compile_shims(&machine);
    quote!(#(#items)* #shims)
}

/// The documented compile-only shims (never emitted on the file lane).
pub(crate) fn compile_shims(machine: &Machine) -> TokenStream {
    let name = &machine.name;
    let name_text = name.to_string();
    let span = name.span();
    let state = Ident::new(&format!("{GENERATED_PREFIX}{name_text}_State"), span);
    let mut wrappers = Vec::new();
    let mut add = |method: &str,
                   free: &str,
                   params: Vec<TokenStream>,
                   args: Vec<TokenStream>,
                   ret: TokenStream| {
        let m = format_ident!("{}", method, span = span);
        let f = Ident::new(&format!("{GENERATED_PREFIX}{name_text}__{free}"), span);
        wrappers.push(quote! {
            #[allow(dead_code)]
            pub fn #m(#(#params),*) #ret { #f(#(#args),*) }
        });
    };
    let st = quote!(#state);
    for tr in &machine.transitions {
        let t = tr.name.to_string();
        let ps: Vec<TokenStream> = tr
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let ty = &p.ty;
                quote!(#n: #ty)
            })
            .collect();
        let pa: Vec<TokenStream> = tr.params.iter().map(|p| p.name.to_token_stream()).collect();
        let b = quote!(-> bool);
        match tr.kind {
            TransitionKind::Init => {
                let mut params = vec![quote!(post: #st)];
                params.extend(ps.clone());
                let mut args = vec![quote!(post)];
                args.extend(pa.clone());
                add(&t, &t, params, args, b.clone());
                add(
                    &format!("{t}_enabled"),
                    &format!("{t}_enabled"),
                    ps.clone(),
                    pa.clone(),
                    b.clone(),
                );
            }
            _ => {
                let mut params = vec![quote!(pre: #st), quote!(post: #st)];
                params.extend(ps.clone());
                let mut args = vec![quote!(pre), quote!(post)];
                args.extend(pa.clone());
                add(&t, &t, params.clone(), args.clone(), b.clone());
                add(
                    &format!("{t}_strong"),
                    &format!("{t}_strong"),
                    params,
                    args,
                    b.clone(),
                );
                let mut params = vec![quote!(pre: #st)];
                params.extend(ps.clone());
                let mut args = vec![quote!(pre)];
                args.extend(pa.clone());
                add(
                    &format!("{t}_enabled"),
                    &format!("{t}_enabled"),
                    params,
                    args,
                    b.clone(),
                );
            }
        }
    }
    let b = quote!(-> bool);
    add(
        "init",
        "init",
        vec![quote!(post: #st)],
        vec![quote!(post)],
        b.clone(),
    );
    add(
        "next",
        "next",
        vec![quote!(pre: #st), quote!(post: #st)],
        vec![quote!(pre), quote!(post)],
        b.clone(),
    );
    add(
        "next_strong",
        "next_strong",
        vec![quote!(pre: #st), quote!(post: #st)],
        vec![quote!(pre), quote!(post)],
        b,
    );
    let mut lemma_wrappers = Vec::new();
    for lemma in &machine.lemmas {
        let ident = &lemma.func.sig.ident;
        let inputs = internal_self_rewrite(lemma.func.sig.inputs.to_token_stream(), name);
        let args: Vec<TokenStream> = lemma
            .func
            .sig
            .inputs
            .iter()
            .filter_map(|arg| match arg {
                syn::FnArg::Typed(pt) => Some(pt.pat.to_token_stream()),
                syn::FnArg::Receiver(_) => None,
            })
            .collect();
        lemma_wrappers.push(quote! {
            #[allow(dead_code)]
            pub fn #ident(#inputs) { #ident(#(#args),*) }
        });
    }
    quote! {
        #[allow(non_snake_case, dead_code)]
        pub mod #name {
            pub use super::#state as State;
        }
        impl #state {
            #(#wrappers)*
            #(#lemma_wrappers)*
        }
    }
}

/// Names of the root items the file lane emits for `machine` (for the
/// compile-lane parity test).
pub(crate) fn file_lane_item_names(machine: &Machine) -> Vec<String> {
    let mut identity = |ts: TokenStream| ts;
    match generate(machine, Lane::File, &mut identity).and_then(parse_items) {
        Ok(items) => items.iter().map(item_label).collect(),
        Err(msg) => vec![format!("error: {msg}")],
    }
}

pub(crate) fn item_label(item: &Item) -> String {
    match item {
        Item::Fn(f) => format!("fn {}", f.sig.ident),
        Item::Struct(s) => format!("struct {}", s.ident),
        Item::Impl(i) => {
            let methods: Vec<String> = i
                .items
                .iter()
                .filter_map(|it| match it {
                    syn::ImplItem::Fn(m) => Some(m.sig.ident.to_string()),
                    _ => None,
                })
                .collect();
            format!(
                "impl {} {{{}}}",
                i.self_ty.to_token_stream(),
                methods.join(",")
            )
        }
        Item::Mod(m) => format!("mod {}", m.ident),
        Item::Macro(m) => format!("macro {}", m.mac.path.to_token_stream()),
        other => format!("other {}", other.to_token_stream()),
    }
}
