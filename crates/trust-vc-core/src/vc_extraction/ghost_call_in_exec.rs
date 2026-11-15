// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Refuses a `Verified` answer for an exec function whose running code calls
//! a spec or proof function.
//!
//! `#[trust_vc::spec]` and `#[trust_vc::proof]` functions are ghost code.
//! Outside a `trust_mc` build their bodies expand to `loop { unreachable!(..)
//! }`, so a call of one at run time panics for every input. The lane reads
//! such a call as the function's value, or a proof function's postcondition,
//! with no panic.
//!
//! The macros reject some of these calls at compile time: the spec or proof
//! macro scans its source file and rejects an exec free function of its own
//! module that calls it by its bare name outside a macro, and, where it can
//! resolve the crate, a path call from elsewhere in the file. A method call
//! (`s.view()`), a path call of a method (`S::view(s)`), a call in the
//! arguments of a std macro (`assert!(inc(x) > x)`, `vec![..]`), the function
//! named as a value (`let g = m::inc;`), a call through a `use` import from
//! another module, and a caller in an `impl` or another file compile and panic.
//!
//! So this module walks the body of an exec function, skipping what does not
//! run in its own code, and looks for a path (a call or a value) or a method
//! call spelled like a ghost function. Skipped:
//!
//! * the function's attributes, which hold its contract;
//! * the arguments of spec and proof macros (`proof_block!`,
//!   `trust_vc::assert!`, `assume!`, `invariant!`, ...), but not those of
//!   `trust_vc::closure!` and `open_local_invariant!`, whose bodies run, nor
//!   of a macro the file defines under a spec macro's name;
//! * a `let` or a block marked `spec`, `proof`, `ghost` or `tracked` (the
//!   form `let ghost x` and `let tracked x` are parsed into);
//! * nested items, which are functions of their own;
//! * a bare-name call, outside a macro, of a ghost function of the target's
//!   own module, from a free function: the audit rejects it at compile time,
//!   so no such program runs (see [`audited_same_module_ghosts`]).
//!
//! A single-segment path bound by a parameter or by a pattern in scope names
//! that binding, not the function. Ghost functions are the spec and proof
//! functions and methods the file declares at any depth, the names a `use ..
//! as ..` gives them, and the spec functions the lane imports from other files
//! of the crate. Names are matched as text, so a same-named function of
//! another module or a std method of that name counts too; that only refuses
//! more.
//!
//! A function marked `external_body` or `external` is trusted and not read.
//! Only the function whose own code makes the call is refused: a caller of it
//! relies on its contract or its body, and a function that panics before it
//! returns meets any claim about its return value.

use std::collections::BTreeSet;
use std::path::Path;

use proc_macro2::{TokenStream, TokenTree};
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{File, ItemFn, Token};

use super::attr_extract::has_external_trusted_attr;
use super::bodiless_call_repeat::is_spec_macro;
use crate::mode::FunctionMode;

/// The tag every refusal from this module starts with.
pub(super) const GHOST_CALL_TAG: &str = "ghost function called from exec code";

/// The refusal message for a `Verified` answer of `func`, or `None` when
/// `func` is not an exec function or its running code names no ghost
/// function. `source_file` adds the spec functions the lane imports from
/// other files of the crate. Without a file, `func` alone is read.
pub(super) fn verified_refusal(
    file: Option<&File>,
    source_file: Option<&Path>,
    func: &ItemFn,
) -> Option<String> {
    if !is_exec(&func.attrs) || has_external_trusted_attr(&func.attrs) {
        return None;
    }
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
    let ghosts = GhostNames::of(file, source_file);
    if ghosts.is_empty() {
        return None;
    }
    let audited = audited_same_module_ghosts(file, func);
    let mut local_macros = LocalMacros::default();
    local_macros.visit_file(file);
    let hit =
        first_running_ghost_call(&ghosts, audited, local_macros.names, &func.sig, &func.block)?;
    Some(message(&format!("`{}`", func.sig.ident), &hit))
}

/// The paths (`b::inc`, without generic arguments) and method calls
/// (`.view`) that the running code of `func` names, or `None` when `func` is
/// not an exec function whose body the lane reads.
pub(super) fn exec_running_call_paths(func: &ItemFn) -> Option<BTreeSet<String>> {
    if !is_exec(&func.attrs) || has_external_trusted_attr(&func.attrs) {
        return None;
    }
    let mut scan = RunningCalls::new(None, &func.sig);
    scan.visit_block(&func.block);
    Some(scan.paths.into_iter().collect())
}

/// True when `attrs` declare an exec function: no spec or proof mode.
fn is_exec(attrs: &[syn::Attribute]) -> bool {
    crate::mode_attrs::classify_attrs(attrs) == FunctionMode::Exec
        && !attrs.iter().any(is_ghost_mode_attr)
}

fn message(what: &str, hit: &str) -> String {
    format!(
        "{GHOST_CALL_TAG}: {what} calls the spec or proof function `{hit}` from code that runs. \
         vc_extraction reads the call as ghost code, the function's value or lemma, while the \
         build runs it (outside a verification build a `#[trust_vc::spec]` or \
         `#[trust_vc::proof]` function panics when called). A `Verified` answer is refused; a \
         refutation would be kept"
    )
}

/// The first path or method call in the running code of `block` that names a
/// ghost function, other than a call the macros' audit rejects (`audited`).
/// `local_macros` are the `macro_rules!` names of the file, which may shadow a
/// spec macro's name.
fn first_running_ghost_call(
    ghosts: &GhostNames,
    audited: BTreeSet<String>,
    local_macros: BTreeSet<String>,
    sig: &syn::Signature,
    block: &syn::Block,
) -> Option<String> {
    let mut scan = RunningCalls::new(Some(ghosts), sig);
    scan.audited = audited;
    scan.local_macros = local_macros;
    scan.visit_block(block);
    scan.hit
}

/// `trust_vc` macros whose arguments hold exec code that runs: a closure body,
/// an invariant-opening block.
const RUNNING_TRUST_VC_MACROS: &[&str] =
    &["closure", "open_local_invariant", "open_atomic_invariant"];

/// The names of the `macro_rules!` macros a file defines, at any depth.
#[derive(Default)]
struct LocalMacros {
    names: BTreeSet<String>,
}

impl<'ast> Visit<'ast> for LocalMacros {
    fn visit_item_macro(&mut self, item: &'ast syn::ItemMacro) {
        if let Some(ident) = &item.ident {
            self.names.insert(unraw(ident));
        }
        syn::visit::visit_item_macro(self, item);
    }
}

/// Attributes that leave a function's tokens as written: built-in ones, and
/// the `trust_vc` markers whose macros return the item unchanged.
const INERT_ATTRS: &[&str] = &[
    "doc",
    "allow",
    "warn",
    "deny",
    "forbid",
    "expect",
    "inline",
    "cold",
    "must_use",
    "track_caller",
    "deprecated",
    "opaque",
    "verifier",
];

/// The ghost functions whose call from `func` the macros' mode audit rejects
/// at compile time, so a program with one does not run.
///
/// The `spec`, `proof`, `broadcast` and `spec_mode` macros read the source
/// file, find the module that declares their function, and reject every exec
/// free function of that module, other than a `#[test]`, whose tokens call
/// the function by its bare name outside a macro. So when `func` is a free
/// function of the file, the audited ghost functions are those its own module
/// declares with one of those macros as the first attribute that can change
/// the tokens the audit compares. A qualified path, a method, a call in macro
/// tokens and a caller in an `impl` are not audited this way.
fn audited_same_module_ghosts(file: &File, func: &ItemFn) -> BTreeSet<String> {
    let is_test = func.attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "test")
    });
    if is_test {
        return BTreeSet::new();
    }
    let mut modules = Vec::new();
    modules_declaring(&file.items, func, &mut modules);
    let [items] = modules.as_slice() else {
        return BTreeSet::new();
    };
    items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(ghost) if runs_the_audit(&ghost.attrs) => Some(unraw(&ghost.sig.ident)),
            _ => None,
        })
        .collect()
}

/// The item lists of the file root and its inline modules, at any depth, that
/// declare `func` as a free function.
fn modules_declaring<'a>(items: &'a [syn::Item], func: &ItemFn, out: &mut Vec<&'a [syn::Item]>) {
    let tokens = quote::ToTokens::to_token_stream(func).to_string();
    let declares = items.iter().any(|item| match item {
        syn::Item::Fn(candidate) => {
            std::ptr::eq(candidate, func)
                || (candidate.sig.ident == func.sig.ident
                    && quote::ToTokens::to_token_stream(candidate).to_string() == tokens)
        }
        _ => false,
    });
    if declares {
        out.push(items);
    }
    for item in items {
        if let syn::Item::Mod(module) = item {
            if let Some((_, inner)) = &module.content {
                modules_declaring(inner, func, out);
            }
        }
    }
}

/// True when the first attribute of a function that can change its tokens is
/// a `trust_vc` macro that runs the mode audit.
fn runs_the_audit(attrs: &[syn::Attribute]) -> bool {
    for attr in attrs {
        let segments: Vec<String> = attr
            .path()
            .segments
            .iter()
            .map(|segment| unraw(&segment.ident))
            .collect();
        let name = match segments.as_slice() {
            [root, name] if root == "trust_vc" => name.as_str(),
            [name] => name.as_str(),
            _ => return false,
        };
        if matches!(name, "spec" | "proof" | "broadcast" | "spec_mode") {
            return true;
        }
        let pass_through = INERT_ATTRS.contains(&name)
            && (segments.len() == 1 || matches!(name, "opaque" | "inline" | "verifier"));
        if !pass_through {
            return false;
        }
    }
    false
}

/// A mode attribute that makes a function, a `let` or a block ghost code.
fn is_ghost_mode_attr(attr: &syn::Attribute) -> bool {
    attr.path().segments.last().is_some_and(|segment| {
        matches!(
            unraw(&segment.ident).as_str(),
            "spec" | "spec_mode" | "proof" | "ghost" | "tracked" | "broadcast"
        )
    })
}

fn is_ghost(attrs: &[syn::Attribute]) -> bool {
    crate::mode_attrs::classify_attrs(attrs) != FunctionMode::Exec
        || attrs.iter().any(is_ghost_mode_attr)
}

fn unraw(ident: &syn::Ident) -> String {
    syn::ext::IdentExt::unraw(ident).to_string()
}

/// The names under which a ghost function can be reached.
#[derive(Default)]
struct GhostNames {
    /// Names a path can end in: every ghost function and method, and every
    /// name a `use .. as ..` gives one.
    paths: BTreeSet<String>,
    /// Names a method call can use: the ghost functions that take `self`.
    methods: BTreeSet<String>,
}

impl GhostNames {
    fn of(file: &File, source_file: Option<&Path>) -> Self {
        let mut names = Self::default();
        let mut collector = GhostDecls { names: &mut names };
        collector.visit_file(file);
        if let Some(source_file) = source_file {
            names.paths.extend(
                crate::spec_function_catalog::SpecFunctionCatalog::from_file_with_crate_imports(
                    file,
                    source_file,
                )
                .spec_names()
                .filter_map(|name| name.rsplit("::").next().map(str::to_string)),
            );
        }
        // `use m::inc as f;` makes `f` a ghost function too, and a rename of
        // a rename as well.
        let mut renames = Renames::default();
        renames.visit_file(file);
        loop {
            let before = names.paths.len();
            for (from, to) in &renames.pairs {
                if names.paths.contains(from) {
                    names.paths.insert(to.clone());
                }
            }
            if names.paths.len() == before {
                break;
            }
        }
        names
    }

    fn is_empty(&self) -> bool {
        self.paths.is_empty() && self.methods.is_empty()
    }
}

/// Collects the ghost functions and methods the file declares, at any depth.
struct GhostDecls<'n> {
    names: &'n mut GhostNames,
}

impl GhostDecls<'_> {
    fn record(&mut self, attrs: &[syn::Attribute], sig: &syn::Signature) {
        if is_ghost(attrs) {
            let name = unraw(&sig.ident);
            if sig.receiver().is_some() {
                self.names.methods.insert(name.clone());
            }
            self.names.paths.insert(name);
        }
    }
}

impl<'ast> Visit<'ast> for GhostDecls<'_> {
    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        self.record(&item.attrs, &item.sig);
        syn::visit::visit_item_fn(self, item);
    }

    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        self.record(&item.attrs, &item.sig);
        syn::visit::visit_impl_item_fn(self, item);
    }

    fn visit_trait_item_fn(&mut self, item: &'ast syn::TraitItemFn) {
        self.record(&item.attrs, &item.sig);
        syn::visit::visit_trait_item_fn(self, item);
    }
}

/// Every `use .. as ..` of the file, at any depth, as (name, new name).
#[derive(Default)]
struct Renames {
    pairs: Vec<(String, String)>,
}

impl<'ast> Visit<'ast> for Renames {
    fn visit_use_rename(&mut self, rename: &'ast syn::UseRename) {
        self.pairs
            .push((unraw(&rename.ident), unraw(&rename.rename)));
    }
}

/// Walks the code of a function body that runs, with the names bound in each
/// scope. With `ghosts`, stops at the first path or method call that names a
/// ghost function; without, records every path and method name it reaches.
struct RunningCalls<'g> {
    ghosts: Option<&'g GhostNames>,
    /// Ghost functions whose bare-name call outside a macro is rejected at
    /// compile time (see [`audited_same_module_ghosts`]).
    audited: BTreeSet<String>,
    /// How many macro invocations enclose the current tokens.
    macro_depth: usize,
    /// The file's own `macro_rules!` names.
    local_macros: BTreeSet<String>,
    scopes: Vec<BTreeSet<String>>,
    hit: Option<String>,
    paths: Vec<String>,
}

impl<'g> RunningCalls<'g> {
    fn new(ghosts: Option<&'g GhostNames>, sig: &syn::Signature) -> Self {
        let mut params = BTreeSet::new();
        for input in &sig.inputs {
            if let syn::FnArg::Typed(typed) = input {
                pat_bindings(&typed.pat, &mut params);
            }
        }
        Self {
            ghosts,
            audited: BTreeSet::new(),
            macro_depth: 0,
            local_macros: BTreeSet::new(),
            scopes: vec![params],
            hit: None,
            paths: Vec::new(),
        }
    }

    fn done(&self) -> bool {
        self.hit.is_some()
    }

    fn is_bound(&self, name: &str) -> bool {
        self.scopes.iter().any(|scope| scope.contains(name))
    }

    fn bind_pat(&mut self, pat: &syn::Pat) {
        let mut names = BTreeSet::new();
        pat_bindings(pat, &mut names);
        if let Some(scope) = self.scopes.last_mut() {
            scope.extend(names);
        }
    }

    fn scoped<F: FnOnce(&mut Self)>(&mut self, pats: &[&syn::Pat], visit: F) {
        let mut names = BTreeSet::new();
        for pat in pats {
            pat_bindings(pat, &mut names);
        }
        self.scopes.push(names);
        visit(self);
        self.scopes.pop();
    }

    fn path(&mut self, path: &syn::Path) {
        if self.done() {
            return;
        }
        if let Some(ident) = path.get_ident() {
            if self.is_bound(&unraw(ident)) {
                return;
            }
        }
        let Some(last) = path.segments.last().map(|segment| unraw(&segment.ident)) else {
            return;
        };
        let rendered = path_string(path);
        match self.ghosts {
            Some(ghosts) => {
                if ghosts.paths.contains(&last) {
                    self.hit = Some(rendered);
                }
            }
            None => self.paths.push(rendered),
        }
    }

    fn method(&mut self, method: &syn::Ident) {
        if self.done() {
            return;
        }
        let name = unraw(method);
        match self.ghosts {
            Some(ghosts) => {
                if ghosts.methods.contains(&name) {
                    self.hit = Some(format!(".{name}(..)"));
                }
            }
            None => self.paths.push(format!(".{name}")),
        }
    }

    /// Reads the tokens of a macro that runs its arguments: as
    /// comma-separated expressions, else as statements, else token by token,
    /// where every identifier not bound in scope counts as a path.
    fn tokens(&mut self, tokens: &TokenStream) {
        if let Ok(exprs) = syn::parse::Parser::parse2(
            Punctuated::<syn::Expr, Token![,]>::parse_terminated,
            tokens.clone(),
        ) {
            for expr in &exprs {
                self.visit_expr(expr);
            }
            return;
        }
        if let Ok(stmts) = syn::parse::Parser::parse2(syn::Block::parse_within, tokens.clone()) {
            self.scoped(&[], |scan| {
                for stmt in &stmts {
                    scan.visit_stmt(stmt);
                }
            });
            return;
        }
        self.raw_tokens(tokens);
    }

    fn raw_tokens(&mut self, tokens: &TokenStream) {
        for tree in tokens.clone() {
            if self.done() {
                return;
            }
            match tree {
                TokenTree::Ident(ident) => {
                    let name = unraw(&ident);
                    if self.is_bound(&name) {
                        continue;
                    }
                    match self.ghosts {
                        Some(ghosts) => {
                            if ghosts.paths.contains(&name) || ghosts.methods.contains(&name) {
                                self.hit = Some(name);
                            }
                        }
                        None => self.paths.push(name),
                    }
                }
                TokenTree::Group(group) => self.raw_tokens(&group.stream()),
                TokenTree::Punct(_) | TokenTree::Literal(_) => {}
            }
        }
    }
}

impl<'ast> Visit<'ast> for RunningCalls<'_> {
    fn visit_item(&mut self, _item: &'ast syn::Item) {}

    fn visit_attribute(&mut self, _attr: &'ast syn::Attribute) {}

    fn visit_pat(&mut self, _pat: &'ast syn::Pat) {}

    fn visit_block(&mut self, block: &'ast syn::Block) {
        self.scoped(&[], |scan| {
            for stmt in &block.stmts {
                scan.visit_stmt(stmt);
            }
        });
    }

    fn visit_local(&mut self, local: &'ast syn::Local) {
        if !is_ghost(&local.attrs) {
            if let Some(init) = &local.init {
                self.visit_expr(&init.expr);
                if let Some((_, diverge)) = &init.diverge {
                    self.visit_expr(diverge);
                }
            }
        }
        self.bind_pat(&local.pat);
    }

    fn visit_expr(&mut self, expr: &'ast syn::Expr) {
        if self.done() {
            return;
        }
        let ghost_block = match expr {
            syn::Expr::Block(block) => is_ghost(&block.attrs),
            syn::Expr::Unsafe(block) => is_ghost(&block.attrs),
            _ => false,
        };
        if !ghost_block {
            syn::visit::visit_expr(self, expr);
        }
    }

    fn visit_expr_path(&mut self, expr: &'ast syn::ExprPath) {
        self.path(&expr.path);
    }

    fn visit_expr_method_call(&mut self, expr: &'ast syn::ExprMethodCall) {
        self.visit_expr(&expr.receiver);
        self.method(&expr.method);
        for arg in &expr.args {
            self.visit_expr(arg);
        }
    }

    fn visit_expr_closure(&mut self, expr: &'ast syn::ExprClosure) {
        let pats: Vec<&syn::Pat> = expr.inputs.iter().collect();
        self.scoped(&pats, |scan| scan.visit_expr(&expr.body));
    }

    fn visit_arm(&mut self, arm: &'ast syn::Arm) {
        self.scoped(&[&arm.pat], |scan| {
            if let Some((_, guard)) = &arm.guard {
                scan.visit_expr(guard);
            }
            scan.visit_expr(&arm.body);
        });
    }

    fn visit_expr_if(&mut self, expr: &'ast syn::ExprIf) {
        self.visit_expr(&expr.cond);
        let mut lets = Vec::new();
        let_patterns(&expr.cond, &mut lets);
        self.scoped(&lets, |scan| scan.visit_block(&expr.then_branch));
        if let Some((_, else_branch)) = &expr.else_branch {
            self.visit_expr(else_branch);
        }
    }

    fn visit_expr_while(&mut self, expr: &'ast syn::ExprWhile) {
        self.visit_expr(&expr.cond);
        let mut lets = Vec::new();
        let_patterns(&expr.cond, &mut lets);
        self.scoped(&lets, |scan| scan.visit_block(&expr.body));
    }

    fn visit_expr_let(&mut self, expr: &'ast syn::ExprLet) {
        self.visit_expr(&expr.expr);
    }

    fn visit_expr_for_loop(&mut self, expr: &'ast syn::ExprForLoop) {
        self.visit_expr(&expr.expr);
        self.scoped(&[&expr.pat], |scan| scan.visit_block(&expr.body));
    }

    fn visit_expr_call(&mut self, expr: &'ast syn::ExprCall) {
        let audited = self.macro_depth == 0
            && matches!(
                &*expr.func,
                syn::Expr::Path(path)
                    if path.qself.is_none()
                        && path.path.leading_colon.is_none()
                        && path.path.segments.len() == 1
                        && path.path.segments.first().is_some_and(|segment| {
                            self.audited.contains(&unraw(&segment.ident))
                        })
            );
        if !audited {
            self.visit_expr(&expr.func);
        }
        for arg in &expr.args {
            self.visit_expr(arg);
        }
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        if self.done() {
            return;
        }
        let name = mac
            .path
            .segments
            .last()
            .map(|segment| unraw(&segment.ident))
            .unwrap_or_default();
        // A macro the file defines is not the spec macro of that name.
        let local = mac.path.segments.len() == 1 && self.local_macros.contains(&name);
        let runs_body = RUNNING_TRUST_VC_MACROS.contains(&name.as_str());
        if is_spec_macro(&mac.path) && !local && !runs_body {
            return;
        }
        self.macro_depth += 1;
        if runs_body {
            self.raw_tokens(&mac.tokens);
        } else {
            self.tokens(&mac.tokens);
        }
        self.macro_depth -= 1;
    }
}

/// `path` as its segment names joined by `::`, without generic arguments.
fn path_string(path: &syn::Path) -> String {
    let segments: Vec<String> = path
        .segments
        .iter()
        .map(|segment| unraw(&segment.ident))
        .collect();
    let joined = segments.join("::");
    if path.leading_colon.is_some() {
        format!("::{joined}")
    } else {
        joined
    }
}

/// The patterns of the `let` conditions in `cond`, through `&&` chains.
fn let_patterns<'a>(cond: &'a syn::Expr, out: &mut Vec<&'a syn::Pat>) {
    match cond {
        syn::Expr::Let(expr_let) => out.push(&expr_let.pat),
        syn::Expr::Binary(binary) if matches!(binary.op, syn::BinOp::And(_)) => {
            let_patterns(&binary.left, out);
            let_patterns(&binary.right, out);
        }
        syn::Expr::Paren(paren) => let_patterns(&paren.expr, out),
        syn::Expr::Group(group) => let_patterns(&group.expr, out),
        _ => {}
    }
}

/// The names `pat` binds.
fn pat_bindings(pat: &syn::Pat, out: &mut BTreeSet<String>) {
    struct Bindings<'o> {
        out: &'o mut BTreeSet<String>,
    }
    impl<'ast> Visit<'ast> for Bindings<'_> {
        fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
            self.out.insert(unraw(&pat.ident));
            syn::visit::visit_pat_ident(self, pat);
        }
        fn visit_expr(&mut self, _expr: &'ast syn::Expr) {}
    }
    Bindings { out }.visit_pat(pat);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The refusal for the free function `f` of `src`, at any module depth.
    fn refusal(src: &str) -> Option<String> {
        struct FindF(Option<ItemFn>);
        impl<'ast> Visit<'ast> for FindF {
            fn visit_item_fn(&mut self, item: &'ast ItemFn) {
                if item.sig.ident == "f" {
                    self.0 = Some(item.clone());
                }
            }
        }
        let file = syn::parse_file(src).expect("fixture parses");
        let mut find = FindF(None);
        find.visit_file(&file);
        let func = find.0.expect("fixture has `fn f`");
        verified_refusal(Some(&file), None, &func)
    }

    const GHOSTS: &str = "mod m { #[trust_vc::spec] pub fn inc(x: u64) -> u64 { x + 1 } \
                          #[trust_vc::proof] pub fn lemma(x: u64) {} } \
                          use m::inc; use m::lemma; use m::inc as g2; \
                          struct S { a: u64 } \
                          impl S { #[trust_vc::spec] fn view(&self) -> u64 { self.a } } \
                          #[spec] fn top(x: u64) -> u64 { x }";

    #[test]
    fn a_ghost_function_reached_by_running_code_is_refused() {
        for body in [
            "fn f(x: u64) -> u64 { m::inc(x) }",
            "fn f(x: u64) -> u64 { inc(x) }",
            "fn f(x: u64) -> u64 { g2(x) }",
            "fn f(s: &S) -> u64 { s.view() }",
            "fn f(s: &S) -> u64 { S::view(s) }",
            "fn f(x: u64) { lemma(x); }",
            "fn f(x: u64) { assert!(inc(x) > x); }",
            "fn f(x: u64) { assert!(top(x) > x); }",
            "fn f(x: u64) -> u64 { let h = top; h(x) }",
            "#[test] fn f(x: u64) -> u64 { top(x) }",
            "mod n { fn f(x: u64) -> u64 { super::top(x) } }",
            "fn f(x: u64) { assert_eq!(inc(x), 1); }",
            "fn f(x: u64) { println!(\"{}\", inc(x)); }",
            "fn f(x: u64) -> u64 { let h = inc; h(x) }",
            "fn f(x: u64) -> u64 { let c = |y: u64| inc(y); c(x) }",
            "fn f(x: u64) -> u64 { if x > 0 { inc(x) } else { 0 } }",
            "fn f(x: u64) -> u64 { match x { 0 => 0, _ => inc(x) } }",
            "fn f(x: u64) { for i in 0..x { inc(i); } }",
            "fn f(x: u64) { while x > 0 { inc(x); } }",
            "fn f(x: u64) -> u64 { let y = { inc(x) }; y }",
            "fn f(x: u64) -> u64 { let inc2 = inc(x); inc2 }",
            "fn f(x: u64) -> u64 { { let inc = 1; } inc(x) }",
            "fn f(x: u64) -> u64 { if let Some(inc) = Some(x) { inc } else { inc(x) } }",
            "fn f(x: u64) -> u64 { let a = inc(x); let inc = 5; a + inc }",
            "fn f(x: u64) -> u64 { let v = vec![inc(x)]; v[0] }",
            "fn f(x: u64) -> u64 { unknown_macro!(inc x) }",
            "fn f(x: u64) -> u64 { let c = trust_vc::closure!(|y: u64| -> u64 { inc(y) }); c(x) }",
            "fn f(x: u64) { open_local_invariant!(i => { inc(x); }); }",
            "macro_rules! ensures { ($e:expr) => { $e }; } fn f(x: u64) { ensures!(inc(x)); }",
            "fn f(x: u64) -> u64 { let Some(y) = Some(inc(x)) else { return 0; }; y }",
        ] {
            let src = format!("{GHOSTS} {body}");
            assert!(
                refusal(&src).is_some_and(|m| m.starts_with(GHOST_CALL_TAG)),
                "{body}"
            );
        }
    }

    #[test]
    fn ghost_code_and_other_names_are_not_refused() {
        for body in [
            "fn f(x: u64) -> u64 { x + 1 }",
            "#[trust_vc::ensures(result == inc(x))] fn f(x: u64) -> u64 { x + 1 }",
            "#[trust_vc::requires(inc(x) > 0)] fn f(x: u64) {}",
            "fn f(x: u64) { trust_vc::assert!(inc(x) > x); }",
            "fn f(x: u64) { trust_vc::proof_block!({ lemma(x); }); }",
            "fn f(x: u64) { proof_block! { lemma(x); } }",
            "fn f(x: u64) { assume!(inc(x) > x); }",
            "fn f(x: u64) { #[trust_vc::spec] let y = inc(x); }",
            "fn f(x: u64) { #[trust_vc::proof] { lemma(x); } }",
            "fn f(x: u64) { while x > 0 { invariant!(inc(x) > 0); } }",
            "fn f(inc: u64) -> u64 { inc }",
            "fn f(x: u64) -> u64 { let inc = x; inc }",
            "fn f(x: u64) -> u64 { let c = |inc: u64| inc; c(x) }",
            "fn f(x: Option<u64>) -> u64 { match x { Some(inc) => inc, None => 0 } }",
            "fn f(x: Option<u64>) -> u64 { if let Some(inc) = x { inc } else { 0 } }",
            "fn f(x: u64) { for inc in 0..x { let _ = inc; } }",
            "fn f(x: u64) -> u64 { fn inner(y: u64) -> u64 { inc(y) } x }",
            "fn f(v: Vec<u64>) -> usize { v.len() }",
            "fn f(s: &S) -> u64 { s.a }",
            "#[trust_vc::spec] fn f(x: u64) -> u64 { inc(x) }",
            "#[trust_vc::proof] fn f(x: u64) { lemma(x); }",
            "#[trust_vc::external_body] fn f(x: u64) -> u64 { inc(x) }",
            "fn f(x: u64) -> u64 { top(x) }",
            "fn f(x: u64) -> u64 { let c = |y: u64| top(y); c(x) }",
        ] {
            let src = format!("{GHOSTS} {body}");
            assert_eq!(refusal(&src), None, "{body}");
        }
    }

    #[test]
    fn a_file_without_ghost_functions_is_not_read() {
        assert_eq!(
            refusal("fn inc(x: u64) -> u64 { x } fn f(x: u64) -> u64 { inc(x) }"),
            None
        );
    }
}
