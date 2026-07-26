// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Crate-level function discovery for trust-vc-annotated Rust functions.

use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use serde::Serialize;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use syn::visit::{self, Visit};

/// A function found in the source tree with trust_vc verification attributes.
#[derive(Debug, Clone)]
pub struct AnnotatedFunction {
    pub file_path: PathBuf,
    pub name: String,
    pub line: usize,
    pub attributes: Vec<String>,
}

/// A trusted source construct rejected by `cargo trust_vc check --no-cheating`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct TrustedConstructFinding {
    pub file_path: PathBuf,
    pub line: usize,
    pub construct: String,
    pub detail: String,
}

/// Marker attribute on a synthetic [`AnnotatedFunction`] whose `name` is a
/// trait-impl CONFORMANCE obligation, not a source function.
///
/// Conformance is an obligation of the IMPL, not of whatever function happens to
/// share the file (see the internal conformance-attribution design note),
/// so each obligation is enumerated as its OWN check target. This is the
/// soundness-critical half of that design: `verify_one` no longer inherits a
/// sibling impl's conformance verdict, so if a bad impl could go unreported by
/// `check` we would certify a file Verus rejects. Every impl gets a target —
/// including an attribute-less overriding impl method and an EMPTY impl
/// (`impl Tr for bool {}`), neither of which carries a `trust_vc` attribute for
/// the AST scan below to find.
pub const TRAIT_CONFORMANCE_ATTR: &str = "trait_conformance";

/// Target emitted when a file's conformance obligations cannot be ENUMERATED.
/// Verifying it re-runs the enumeration and surfaces the failure, so an
/// un-enumerable file fails CLOSED rather than silently contributing zero
/// conformance targets.
pub const CONFORMANCE_ENUMERATION_FAILED: &str = "trait conformance enumeration failed";

/// True when `func` names a trait-impl conformance obligation rather than a
/// source function.
pub fn is_trait_conformance_target(func: &AnnotatedFunction) -> bool {
    func.attributes
        .iter()
        .any(|attr| attr == TRAIT_CONFORMANCE_ATTR)
}

/// TrustVc attribute names that mark a function for verification.
const TRUST_VC_ATTRS: &[&str] = &[
    // Contract
    "requires",
    "ensures",
    "cite",
    // Proof
    "proof",
    "spec",
    // Meta
    "decreases",
    "opaque",
    "inline",
    "rlimit",
    "external",
    "external_body",
    "broadcast",
    "trigger",
    "trait_spec",
    "trait_impl",
    "contract",
];

const TRUSTED_ATTRS: &[(&str, &str)] = &[
    ("external_body", "trusted function body"),
    ("external", "trusted external function"),
    ("assume_specification", "assumed specification"),
    (
        "assume_termination",
        "assumed termination proof; #[verifier::assume_termination] not allowed with --no-cheating",
    ),
];

const TRUSTED_MACROS_OR_CALLS: &[(&str, &str)] = &[
    ("assume", "source assumption"),
    ("assume_by", "scoped source assumption"),
    ("cite", "cited source assumption (trusted, not proven)"),
    ("admit", "admitted proof"),
    ("external_body", "trusted function body"),
    ("external", "trusted external function"),
    ("assume_specification", "assumed specification"),
    (
        "assume_termination",
        "assumed termination proof; #[verifier::assume_termination] not allowed with --no-cheating",
    ),
    ("external_spec", "trusted external specification"),
    ("extern_spec", "trusted external specification"),
];

/// Scans all `.rs` files under `root/src/` and returns functions with trust_vc attributes.
pub fn scan_crate(root: &Path) -> Vec<AnnotatedFunction> {
    let src_dir = root.join("src");
    if !src_dir.is_dir() {
        return Vec::new();
    }
    let mut results = Vec::new();
    walk_rs_files(&src_dir, &mut results);
    results.sort_by_key(|entry| (entry.file_path.clone(), entry.line));
    results
}

/// Scans a single `.rs` file and returns annotated functions.
pub fn scan_file(path: &Path) -> Vec<AnnotatedFunction> {
    let content = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(err) => {
            eprintln!("trust_vc scan: cannot read {}: {err}", path.display());
            return Vec::new();
        }
    };
    // Strip any `global size_of usize == N` pointer-width directive lines (Verus
    // surface syntax, not valid Rust at item position) before parsing, preserving
    // line offsets so diagnostics stay accurate. Without this, a corpus file that
    // declares the directive fails to parse and yields ZERO discovered functions.
    let content = trust_vc_core::ir::strip_pointer_width_directives(&content);
    let ast = match trust_vc_core::parse_file_allow_tracked(&content) {
        Ok(a) => a,
        Err(err) => {
            eprintln!("trust_vc scan: parse error in {}: {err}", path.display());
            return Vec::new();
        }
    };
    let mut functions = extract_annotated_functions(path, &ast);
    extract_conformance_obligations(path, &ast, &mut functions);
    functions
}

/// Appends the file's trait-impl CONFORMANCE obligations as their own check
/// targets.
///
/// The AST scan above only finds items that CARRY a `trust_vc` attribute, so an
/// overriding impl method with no attributes of its own — and an EMPTY impl,
/// which has no method item at all — are invisible to it. Both are still
/// conformance-checked, so both must be enumerated here or `cargo trust-vc
/// check` would report a clean file where Verus errors. The obligation names come
/// from the verifier itself (the same walk that verifies them), so the target set
/// cannot drift from the checked set.
fn extract_conformance_obligations(
    file_path: &Path,
    ast: &syn::File,
    functions: &mut Vec<AnnotatedFunction>,
) {
    // Cheap gate: a file with no `#[trust_vc::trait_spec]` / `#[trust_vc::trait_impl]`
    // item registers no trait or impl decls, so it has no conformance obligations
    // and needs no (costly) file-level extraction.
    if !declares_trait_items(&ast.items) {
        return;
    }

    let conformance_target = |name: String| AnnotatedFunction {
        file_path: file_path.to_path_buf(),
        name,
        line: 1,
        attributes: vec![TRAIT_CONFORMANCE_ATTR.to_string()],
    };

    let Some(path_str) = file_path.to_str() else {
        functions.push(conformance_target(
            CONFORMANCE_ENUMERATION_FAILED.to_string(),
        ));
        return;
    };
    match trust_vc_core::list_trait_conformance_obligations(path_str) {
        Ok(names) => functions.extend(names.into_iter().map(conformance_target)),
        Err(err) => {
            eprintln!(
                "trust_vc scan: cannot enumerate trait conformance obligations in {}: {err}",
                file_path.display()
            );
            functions.push(conformance_target(
                CONFORMANCE_ENUMERATION_FAILED.to_string(),
            ));
        }
    }
}

/// True when `items` declares a `#[trust_vc::trait_spec]` trait or a
/// `#[trust_vc::trait_impl]` impl (recursing into inline modules) — the only
/// source constructs that register trait/impl decls, hence the only ones that can
/// produce a conformance obligation.
fn declares_trait_items(items: &[syn::Item]) -> bool {
    items.iter().any(|item| match item {
        syn::Item::Trait(item_trait) => attrs_name_trust_vc_trait_item(&item_trait.attrs),
        syn::Item::Impl(item_impl) => attrs_name_trust_vc_trait_item(&item_impl.attrs),
        syn::Item::Mod(module) => module
            .content
            .as_ref()
            .is_some_and(|(_, inner)| declares_trait_items(inner)),
        _ => false,
    })
}

fn attrs_name_trust_vc_trait_item(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let mut names = Vec::new();
        collect_trust_vc_attr_names(attr, &mut names);
        names
            .iter()
            .any(|name| name == "trait_spec" || name == "trait_impl")
    })
}

/// Scans all `.rs` files under `root/src/` for trusted source constructs.
pub fn scan_crate_trusted_constructs(root: &Path) -> Vec<TrustedConstructFinding> {
    let src_dir = root.join("src");
    if !src_dir.is_dir() {
        return Vec::new();
    }
    let mut findings = Vec::new();
    walk_rs_files_for_trusted_constructs(&src_dir, &mut findings);
    findings.sort_by_key(|entry| {
        (
            entry.file_path.clone(),
            entry.line,
            entry.construct.clone(),
            entry.detail.clone(),
        )
    });
    findings
}

/// Scans a single `.rs` file for trusted source constructs.
pub fn scan_file_trusted_constructs(path: &Path) -> Vec<TrustedConstructFinding> {
    let content = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(err) => {
            return vec![TrustedConstructFinding {
                file_path: path.to_path_buf(),
                line: 1,
                construct: "unscannable_source".to_string(),
                detail: format!("cannot read source: {err}"),
            }];
        }
    };
    let content = trust_vc_core::ir::strip_pointer_width_directives(&content);
    let ast = match trust_vc_core::parse_file_allow_tracked(&content) {
        Ok(a) => a,
        Err(err) => {
            return vec![TrustedConstructFinding {
                file_path: path.to_path_buf(),
                line: err.span().start().line.max(1),
                construct: "unscannable_source".to_string(),
                detail: format!("cannot parse source while enforcing --no-cheating: {err}"),
            }];
        }
    };
    let mut visitor = TrustedConstructVisitor::new(path);
    visitor.collect_aliases_from_items(&ast.items);
    visitor.visit_file(&ast);
    visitor.findings
}

fn walk_rs_files(dir: &Path, results: &mut Vec<AnnotatedFunction>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            walk_rs_files(&path, results);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            results.extend(scan_file(&path));
        }
    }
}

fn walk_rs_files_for_trusted_constructs(dir: &Path, results: &mut Vec<TrustedConstructFinding>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            walk_rs_files_for_trusted_constructs(&path, results);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            results.extend(scan_file_trusted_constructs(&path));
        }
    }
}

fn extract_annotated_functions(file_path: &Path, ast: &syn::File) -> Vec<AnnotatedFunction> {
    let mut functions = Vec::new();
    extract_from_items(file_path, &ast.items, &mut functions);
    functions
}

fn extract_from_items(
    file_path: &Path,
    items: &[syn::Item],
    functions: &mut Vec<AnnotatedFunction>,
) {
    for item in items {
        match item {
            syn::Item::Fn(func) => {
                let attrs = trust_vc_attrs_on(&func.attrs);
                if !attrs.is_empty() {
                    functions.push(AnnotatedFunction {
                        file_path: file_path.to_path_buf(),
                        name: func.sig.ident.to_string(),
                        line: func.sig.ident.span().start().line,
                        attributes: attrs,
                    });
                }
            }
            syn::Item::Impl(impl_block) => {
                for impl_item in &impl_block.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        let attrs = trust_vc_attrs_on(&method.attrs);
                        if !attrs.is_empty() {
                            functions.push(AnnotatedFunction {
                                file_path: file_path.to_path_buf(),
                                name: method.sig.ident.to_string(),
                                line: method.sig.ident.span().start().line,
                                attributes: attrs,
                            });
                        }
                    }
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, ref items)) = module.content {
                    extract_from_items(file_path, items, functions);
                }
            }
            syn::Item::Trait(trait_block) => {
                for trait_item in &trait_block.items {
                    if let syn::TraitItem::Fn(method) = trait_item {
                        let attrs = trust_vc_attrs_on(&method.attrs);
                        if !attrs.is_empty() {
                            functions.push(AnnotatedFunction {
                                file_path: file_path.to_path_buf(),
                                name: method.sig.ident.to_string(),
                                line: method.sig.ident.span().start().line,
                                attributes: attrs,
                            });
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

fn trust_vc_attrs_on(attrs: &[syn::Attribute]) -> Vec<String> {
    let mut found = Vec::new();
    for attr in attrs {
        collect_trust_vc_attr_names(attr, &mut found);
    }
    found
}

/// Record the trust_vc attribute name(s) carried by a single attribute, seeing
/// through a `#[cfg_attr(<pred>, <attr>)]` wrapper.
///
/// A `#[cfg_attr(trust_vc, trust_vc::contract(...))]` on the real solver function
/// expands to nothing in a normal compile (the `trust_vc` cfg is never set), so it
/// is inert and the binary is unchanged. But because `cargo trust_vc check`
/// verifies from *source* (via `syn`, never compiling the crate), we deliberately
/// unwrap the `cfg_attr` here — regardless of its predicate — and treat an inner
/// trust_vc attribute as if it were applied directly. This lets the proof live on
/// the literal solver function without pulling a `trust_vc` dependency into the
/// competition build.
fn collect_trust_vc_attr_names(attr: &syn::Attribute, found: &mut Vec<String>) {
    if attr_path_is_cfg_attr(attr.path()) {
        for inner in cfg_attr_inner_metas(attr) {
            if let Some(name) = meta_trust_vc_attr_name(&inner) {
                found.push(name);
            }
        }
        return;
    }
    if let Some(last_seg) = attr.path().segments.last() {
        let name = last_seg.ident.to_string();
        if TRUST_VC_ATTRS.contains(&name.as_str()) {
            found.push(name);
        }
    }
}

/// True when an attribute path is exactly `cfg_attr` (last segment `cfg_attr`).
fn attr_path_is_cfg_attr(path: &syn::Path) -> bool {
    path.segments
        .last()
        .is_some_and(|segment| segment.ident == "cfg_attr")
}

/// Parse the inner attribute metas of a `#[cfg_attr(<pred>, <attr>, ...)]`,
/// dropping the leading predicate. Returns the inner `syn::Meta` items (e.g.
/// `trust_vc::contract(ensures(ret >= 0), returns(ret))`).
fn cfg_attr_inner_metas(attr: &syn::Attribute) -> Vec<syn::Meta> {
    let syn::Meta::List(meta_list) = &attr.meta else {
        return Vec::new();
    };
    // `cfg_attr` args are `<pred>, <attr1>, <attr2>, ...` — a comma-separated
    // list of `Meta`. The first element is the cfg predicate; the rest are the
    // attributes to apply.
    let parsed = meta_list.parse_args_with(
        syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated,
    );
    match parsed {
        Ok(list) => list.into_iter().skip(1).collect(),
        Err(_) => Vec::new(),
    }
}

/// If a `Meta` names a trust_vc attribute (by last path segment), return its name.
fn meta_trust_vc_attr_name(meta: &syn::Meta) -> Option<String> {
    let name = meta.path().segments.last()?.ident.to_string();
    TRUST_VC_ATTRS.contains(&name.as_str()).then_some(name)
}

fn path_last_ident(path: &syn::Path) -> Option<String> {
    path.segments
        .last()
        .map(|segment| segment.ident.to_string())
}

fn trusted_attr_detail(name: &str) -> Option<&'static str> {
    TRUSTED_ATTRS
        .iter()
        .find_map(|(construct, detail)| (*construct == name).then_some(*detail))
}

fn trusted_macro_or_call_detail(name: &str) -> Option<&'static str> {
    TRUSTED_MACROS_OR_CALLS
        .iter()
        .find_map(|(construct, detail)| (*construct == name).then_some(*detail))
}

fn span_line(span: Span) -> usize {
    span.start().line.max(1)
}

#[derive(Clone, Copy)]
enum TokenScanMode {
    Attribute,
    MacroBody,
}

#[derive(Debug, Clone)]
struct TrustedAlias {
    construct: String,
    attr_detail: Option<&'static str>,
    macro_or_call_detail: Option<&'static str>,
}

struct TrustedConstructVisitor {
    file_path: PathBuf,
    findings: Vec<TrustedConstructFinding>,
    aliases: BTreeMap<String, TrustedAlias>,
    /// Formatted `proof_note`/`custom_err` suffix from the ENCLOSING macro
    /// statement's attributes, appended to the finding detail so the
    /// `--no-cheating` channel carries the user's label text (Verus parity:
    /// `test_proof_note_on_assume_with_no_cheating` expects
    /// "note: Statement known to be false" in the diagnostic;
    /// `test_custom_err_on_assume_with_no_cheating` expects the raw
    /// replacement text).
    pending_macro_note: Option<String>,
}

/// Renders the proof-note suffix for a finding detail from a single label:
/// `proof_note` keeps the primary detail and appends "note: {text}"
/// (secondary-label channel); `custom_err` appends the raw replacement text.
/// Exactly one label produces a suffix — malformed or duplicate labels
/// produce none here (the verification path itself rejects duplicates with
/// the upstream at-most-one error).
fn proof_note_suffix_from_attrs(attrs: &[syn::Attribute]) -> Option<String> {
    let labels = trust_vc_core::proof_note::proof_note_labels_from_attrs(attrs).ok()?;
    proof_note_suffix_from_labels(labels)
}

fn proof_note_suffix_from_tokens(tokens: &TokenStream) -> Option<String> {
    let mut expr = syn::parse2::<syn::Expr>(tokens.clone()).ok()?;
    let labels = trust_vc_core::proof_note::take_leading_proof_note_labels(&mut expr).ok()?;
    proof_note_suffix_from_labels(labels)
}

fn proof_note_suffix_from_labels(
    labels: Vec<trust_vc_core::proof_note::ProofNoteLabel>,
) -> Option<String> {
    let [label] = labels.as_slice() else {
        return None;
    };
    if label.is_custom_err {
        Some(format!("; {}", label.text))
    } else {
        Some(format!("; note: {}", label.text))
    }
}

impl TrustedConstructVisitor {
    fn new(file_path: &Path) -> Self {
        Self {
            file_path: file_path.to_path_buf(),
            findings: Vec::new(),
            aliases: BTreeMap::new(),
            pending_macro_note: None,
        }
    }

    fn push(&mut self, line: usize, construct: impl Into<String>, detail: impl Into<String>) {
        self.findings.push(TrustedConstructFinding {
            file_path: self.file_path.clone(),
            line,
            construct: construct.into(),
            detail: detail.into(),
        });
    }

    fn collect_aliases_from_items(&mut self, items: &[syn::Item]) {
        for item in items {
            match item {
                syn::Item::Use(item_use) => {
                    self.collect_aliases_from_use_tree(Vec::new(), &item_use.tree);
                }
                syn::Item::Mod(module) => {
                    if let Some((_, items)) = &module.content {
                        self.collect_aliases_from_items(items);
                    }
                }
                _ => {}
            }
        }
    }

    fn collect_aliases_from_use_tree(&mut self, mut prefix: Vec<String>, tree: &syn::UseTree) {
        match tree {
            syn::UseTree::Path(path) => {
                prefix.push(path.ident.to_string());
                self.collect_aliases_from_use_tree(prefix, &path.tree);
            }
            syn::UseTree::Name(name) => {
                self.record_trusted_import_alias(&prefix, &name.ident.to_string(), &name.ident);
            }
            syn::UseTree::Rename(rename) => {
                self.record_trusted_import_alias(
                    &prefix,
                    &rename.ident.to_string(),
                    &rename.rename,
                );
            }
            syn::UseTree::Group(group) => {
                for tree in &group.items {
                    self.collect_aliases_from_use_tree(prefix.clone(), tree);
                }
            }
            syn::UseTree::Glob(_) => {}
        }
    }

    fn record_trusted_import_alias(
        &mut self,
        _prefix: &[String],
        imported_name: &str,
        visible_ident: &syn::Ident,
    ) {
        let attr_detail = trusted_attr_detail(imported_name);
        let macro_or_call_detail = trusted_macro_or_call_detail(imported_name);
        if attr_detail.is_none() && macro_or_call_detail.is_none() {
            return;
        }

        self.aliases
            .entry(visible_ident.to_string())
            .or_insert_with(|| TrustedAlias {
                construct: imported_name.to_string(),
                attr_detail,
                macro_or_call_detail,
            });
    }

    fn trusted_attr_for_name(&self, name: &str) -> Option<(String, &'static str)> {
        trusted_attr_detail(name)
            .map(|detail| (name.to_string(), detail))
            .or_else(|| {
                self.aliases.get(name).and_then(|alias| {
                    alias
                        .attr_detail
                        .map(|detail| (alias.construct.clone(), detail))
                })
            })
    }

    fn trusted_macro_or_call_for_name(&self, name: &str) -> Option<(String, &'static str)> {
        trusted_macro_or_call_detail(name)
            .map(|detail| (name.to_string(), detail))
            .or_else(|| {
                self.aliases.get(name).and_then(|alias| {
                    alias
                        .macro_or_call_detail
                        .map(|detail| (alias.construct.clone(), detail))
                })
            })
    }

    fn trusted_spelling(&self, visible_name: &str, rendered: &str, construct: &str) -> String {
        if visible_name == construct {
            format!("`{rendered}`")
        } else {
            format!("`{rendered}` alias for `{construct}`")
        }
    }

    fn inspect_attribute(&mut self, attr: &syn::Attribute) {
        if let Some(name) = path_last_ident(attr.path()) {
            if let Some((construct, detail)) = self.trusted_attr_for_name(&name) {
                let line = attr
                    .path()
                    .segments
                    .last()
                    .map(|segment| span_line(segment.ident.span()))
                    .unwrap_or(1);
                self.push(
                    line,
                    construct.clone(),
                    format!(
                        "{detail}: {}",
                        self.trusted_spelling(&name, &format!("#[{name}]"), &construct)
                    ),
                );
            }
        }

        if let syn::Meta::List(meta) = &attr.meta {
            self.scan_tokens(&meta.tokens, TokenScanMode::Attribute);
        }
    }

    fn inspect_via_fn_attrs(&mut self, attrs: &[syn::Attribute], ident: &syn::Ident) {
        let mut has_via_fn = false;
        let mut trusted_body_attr: Option<String> = None;
        for attr in attrs {
            let Some(name) = path_last_ident(attr.path()) else {
                continue;
            };
            if name == "via_fn" {
                has_via_fn = true;
            } else if let Some((construct, _)) = self.trusted_attr_for_name(&name) {
                if matches!(construct.as_str(), "external_body" | "external") {
                    trusted_body_attr = Some(construct);
                }
            }
        }

        if has_via_fn {
            if let Some(attr) = trusted_body_attr {
                self.push(
                    span_line(ident.span()),
                    "via_fn_external_body",
                    format!("via function `{ident}` is backed by trusted `#[{attr}]`"),
                );
            }
        }
    }

    fn scan_tokens(&mut self, tokens: &TokenStream, mode: TokenScanMode) {
        let tokens = tokens.clone().into_iter().collect::<Vec<_>>();
        for (index, token) in tokens.iter().enumerate() {
            match token {
                TokenTree::Ident(ident) => {
                    let name = ident.to_string();
                    match mode {
                        TokenScanMode::Attribute => {
                            if let Some((construct, detail)) = self.trusted_attr_for_name(&name) {
                                self.push(
                                    span_line(ident.span()),
                                    construct.clone(),
                                    format!(
                                        "{detail}: attribute metadata {}",
                                        self.trusted_spelling(&name, &name, &construct)
                                    ),
                                );
                            }
                        }
                        TokenScanMode::MacroBody => {
                            if let Some((construct, detail)) =
                                self.trusted_macro_or_call_for_name(&name)
                            {
                                let spelling = if token_is_followed_by_bang(&tokens, index) {
                                    format!("{name}!")
                                } else if token_is_followed_by_call_group(&tokens, index) {
                                    format!("{name}(...)")
                                } else {
                                    name.clone()
                                };
                                let context = if token_starts_macro_or_call(&tokens, index) {
                                    format!(
                                        "{detail}: nested {} in macro tokens",
                                        self.trusted_spelling(&name, &spelling, &construct)
                                    )
                                } else {
                                    format!(
                                        "{detail}: forwarded {} in macro tokens",
                                        self.trusted_spelling(&name, &spelling, &construct)
                                    )
                                };
                                self.push(span_line(ident.span()), construct, context);
                            }
                        }
                    }
                }
                TokenTree::Group(group) => self.scan_tokens(&group.stream(), mode),
                _ => {}
            }
        }
    }
}

fn token_is_followed_by_bang(tokens: &[TokenTree], index: usize) -> bool {
    matches!(
        tokens.get(index + 1),
        Some(TokenTree::Punct(punct)) if punct.as_char() == '!'
    )
}

fn token_is_followed_by_call_group(tokens: &[TokenTree], index: usize) -> bool {
    matches!(
        tokens.get(index + 1),
        Some(TokenTree::Group(group)) if group.delimiter() == Delimiter::Parenthesis
    )
}

fn token_starts_macro_or_call(tokens: &[TokenTree], index: usize) -> bool {
    token_is_followed_by_bang(tokens, index) || token_is_followed_by_call_group(tokens, index)
}

impl<'ast> Visit<'ast> for TrustedConstructVisitor {
    fn visit_attribute(&mut self, attr: &'ast syn::Attribute) {
        self.inspect_attribute(attr);
        visit::visit_attribute(self, attr);
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        self.inspect_via_fn_attrs(&item.attrs, &item.sig.ident);
        visit::visit_item_fn(self, item);
    }

    fn visit_stmt_macro(&mut self, stmt_macro: &'ast syn::StmtMacro) {
        // Capture the statement-level proof-note label so the trusted-macro
        // finding for this statement carries the user's label text.
        let saved = self.pending_macro_note.take();
        self.pending_macro_note = proof_note_suffix_from_attrs(&stmt_macro.attrs);
        visit::visit_stmt_macro(self, stmt_macro);
        self.pending_macro_note = saved;
    }

    fn visit_expr_macro(&mut self, expr_macro: &'ast syn::ExprMacro) {
        let saved = self.pending_macro_note.take();
        self.pending_macro_note = proof_note_suffix_from_attrs(&expr_macro.attrs);
        visit::visit_expr_macro(self, expr_macro);
        self.pending_macro_note = saved;
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        if let Some(name) = path_last_ident(&mac.path) {
            if let Some((construct, detail)) = self.trusted_macro_or_call_for_name(&name) {
                let line = mac
                    .path
                    .segments
                    .last()
                    .map(|segment| span_line(segment.ident.span()))
                    .unwrap_or(1);
                // Prefer the statement-level label; fall back to an
                // expression-level label inside the macro tokens (upstream
                // moves statement attrs inside onto the argument expression,
                // so both spellings are the same label position).
                let note = self
                    .pending_macro_note
                    .clone()
                    .or_else(|| proof_note_suffix_from_tokens(&mac.tokens))
                    .unwrap_or_default();
                self.push(
                    line,
                    construct.clone(),
                    format!(
                        "{detail}: {}{note}",
                        self.trusted_spelling(&name, &format!("{name}!"), &construct)
                    ),
                );
            }
        }
        self.scan_tokens(&mac.tokens, TokenScanMode::MacroBody);
        visit::visit_macro(self, mac);
    }

    fn visit_expr_call(&mut self, expr: &'ast syn::ExprCall) {
        if let syn::Expr::Path(path) = expr.func.as_ref() {
            if let Some(name) = path_last_ident(&path.path) {
                if let Some((construct, detail)) = self.trusted_macro_or_call_for_name(&name) {
                    let line = path
                        .path
                        .segments
                        .last()
                        .map(|segment| span_line(segment.ident.span()))
                        .unwrap_or(1);
                    self.push(
                        line,
                        construct.clone(),
                        format!(
                            "{detail}: {}",
                            self.trusted_spelling(&name, &format!("{name}(...)"), &construct)
                        ),
                    );
                }
            }
        }
        visit::visit_expr_call(self, expr);
    }

    fn visit_item_foreign_mod(&mut self, item: &'ast syn::ItemForeignMod) {
        self.push(
            span_line(item.abi.extern_token.span),
            "external",
            "trusted external declarations: `extern` block",
        );
        visit::visit_item_foreign_mod(self, item);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scan_file_finds_annotated_functions() {
        let source = r#"
            #[requires(x > 0)]
            #[ensures(result > 0)]
            fn add_positive(x: u32) -> u32 {
                x + 1
            }

            fn plain_function() {}

            #[proof]
            fn lemma_something() {}
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_scan_test.rs");
        std::fs::write(&tmp, source).unwrap();
        let funcs = scan_file(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert_eq!(funcs.len(), 2);
        assert_eq!(funcs[0].name, "add_positive");
        assert!(funcs[0].attributes.contains(&"requires".to_string()));
        assert!(funcs[0].attributes.contains(&"ensures".to_string()));
        assert_eq!(funcs[1].name, "lemma_something");
        assert!(funcs[1].attributes.contains(&"proof".to_string()));
    }

    #[test]
    fn test_scan_file_sees_cfg_attr_wrapped_contract() {
        // A contract gated behind `#[cfg_attr(trust_vc, ...)]` is inert in a
        // normal compile (the `trust_vc` cfg is never set), but `cargo trust_vc
        // check` reads source and must still discover + verify it.
        let source = r#"
            #[cfg_attr(trust_vc, trust_vc::contract(ensures(ret >= 0), returns(ret)))]
            fn shortfall_for(x: i128) -> i128 {
                x.max(0)
            }

            fn plain_function() {}
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_scan_cfg_attr_contract.rs");
        std::fs::write(&tmp, source).unwrap();
        let funcs = scan_file(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert_eq!(
            funcs.len(),
            1,
            "cfg_attr-wrapped contract not discovered: {funcs:?}"
        );
        assert_eq!(funcs[0].name, "shortfall_for");
        assert!(
            funcs[0].attributes.contains(&"contract".to_string()),
            "cfg_attr inner `contract` not recognized: {:?}",
            funcs[0].attributes
        );
    }

    #[test]
    fn test_scan_file_allows_bare_assert_forall_by_statement() {
        let source = r#"
            #[ensures(true)]
            fn proof() {
                assert forall |k: u32| k == k by {};
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_scan_test_assert_forall_by.rs");
        std::fs::write(&tmp, source).unwrap();
        let funcs = scan_file(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "proof");
        assert!(funcs[0].attributes.contains(&"ensures".to_string()));
    }

    #[test]
    fn test_scan_file_ignores_non_trust_vc_attrs() {
        let source = r#"
            #[derive(Debug)]
            #[inline]
            fn regular() {}
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_scan_test_ignore.rs");
        std::fs::write(&tmp, source).unwrap();
        let funcs = scan_file(&tmp);
        std::fs::remove_file(&tmp).ok();

        // `#[inline]` is a trust_vc attribute (opaque-control for spec functions),
        // but `#[derive(Debug)]` is not, so we still find the function.
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "regular");
        assert!(funcs[0].attributes.contains(&"inline".to_string()));
    }

    /// SOUNDNESS-CRITICAL (attribution). `check` no longer inherits a sibling
    /// impl's conformance verdict, so an impl is reported ONLY through its own
    /// target. Two shapes the attribute scan cannot see must still be enumerated:
    /// an EMPTY impl (`impl Tr for bool {}` — no method item at all) and an
    /// overriding impl method carrying no `trust_vc` attribute of its own. If
    /// either goes untargeted, a bad impl is never checked and `cargo trust-vc
    /// check` certifies a file Verus rejects.
    #[test]
    fn test_scan_file_enumerates_conformance_obligations_the_attr_scan_cannot_see() {
        let source = r#"
            #[trust_vc::trait_spec]
            trait Empty: Sized {
                #[trust_vc::ensures(result)]
                fn m(self) -> bool { false }
            }

            #[trust_vc::trait_impl]
            impl Empty for bool {}

            #[trust_vc::trait_spec]
            trait Plain {
                #[trust_vc::ensures(result >= 10)]
                fn get(&self) -> i32;
            }

            struct Widget(i32);

            #[trust_vc::trait_impl]
            impl Plain for Widget {
                fn get(&self) -> i32 { 0 }
            }
        "#;
        let tmp = std::env::temp_dir().join(format!(
            "trust_vc_scan_conformance_{}.rs",
            std::process::id()
        ));
        std::fs::write(&tmp, source).unwrap();
        let funcs = scan_file(&tmp);
        std::fs::remove_file(&tmp).ok();

        let conformance: Vec<&str> = funcs
            .iter()
            .filter(|f| is_trait_conformance_target(f))
            .map(|f| f.name.as_str())
            .collect();
        assert!(
            conformance.contains(&"trait impl conformance Empty::m for bool"),
            "an EMPTY impl has no method item for the attribute scan to find — its inherited \
             default body must still be a check target: {conformance:?}"
        );
        assert!(
            conformance.contains(&"trait impl conformance Plain::get for Widget"),
            "an impl method with no trust_vc attribute of its own must still be a check \
             target: {conformance:?}"
        );
    }

    /// A file with no trait items gains no conformance targets (the cheap gate
    /// must not add spurious work or spurious cases).
    #[test]
    fn test_scan_file_without_trait_items_adds_no_conformance_targets() {
        let source = r#"
            #[requires(x > 0)]
            #[ensures(result > 0)]
            fn add_positive(x: u32) -> u32 { x + 1 }
        "#;
        let tmp = std::env::temp_dir().join(format!(
            "trust_vc_scan_no_conformance_{}.rs",
            std::process::id()
        ));
        std::fs::write(&tmp, source).unwrap();
        let funcs = scan_file(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert!(
            !funcs.iter().any(is_trait_conformance_target),
            "a trait-free file must produce no conformance targets: {funcs:?}"
        );
    }

    #[test]
    fn test_scan_crate_no_src_dir() {
        let tmp = std::env::temp_dir().join("trust_vc_scan_nosrc");
        std::fs::create_dir_all(&tmp).ok();
        let funcs = scan_crate(&tmp);
        std::fs::remove_dir_all(&tmp).ok();
        assert!(funcs.is_empty());
    }

    #[test]
    fn test_scan_file_discovers_methods_in_impl_blocks() {
        let source = r#"
            struct Counter { value: u32 }

            impl Counter {
                #[requires(self.value < u32::MAX)]
                #[ensures(result == self.value + 1)]
                fn increment(&self) -> u32 {
                    self.value + 1
                }

                fn plain_method(&self) {}
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_scan_impl.rs");
        std::fs::write(&tmp, source).unwrap();
        let funcs = scan_file(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "increment");
        assert!(funcs[0].attributes.contains(&"requires".to_string()));
        assert!(funcs[0].attributes.contains(&"ensures".to_string()));
    }

    #[test]
    fn test_scan_file_discovers_functions_in_inline_modules() {
        let source = r#"
            mod inner {
                #[ensures(result == x)]
                fn identity(x: i32) -> i32 {
                    x
                }
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_scan_mod.rs");
        std::fs::write(&tmp, source).unwrap();
        let funcs = scan_file(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "identity");
        assert!(funcs[0].attributes.contains(&"ensures".to_string()));
    }

    #[test]
    fn test_scan_file_discovers_trait_default_methods() {
        let source = r#"
            trait Verifiable {
                #[ensures(result > 0)]
                fn positive(&self) -> u32 {
                    1
                }

                fn unverified(&self);
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_scan_trait.rs");
        std::fs::write(&tmp, source).unwrap();
        let funcs = scan_file(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "positive");
        assert!(funcs[0].attributes.contains(&"ensures".to_string()));
    }

    #[test]
    fn test_scan_file_discovers_both_top_level_and_impl_functions() {
        let source = r#"
            #[ensures(result == x)]
            fn top_level(x: i32) -> i32 { x }

            struct Foo;
            impl Foo {
                #[requires(x > 0)]
                fn method(x: u32) -> u32 { x }
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_scan_mixed.rs");
        std::fs::write(&tmp, source).unwrap();
        let funcs = scan_file(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert_eq!(funcs.len(), 2);
        let names: Vec<&str> = funcs.iter().map(|f| f.name.as_str()).collect();
        assert!(names.contains(&"top_level"));
        assert!(names.contains(&"method"));
    }

    #[test]
    fn test_no_cheating_scan_accepts_ordinary_contracts() {
        let source = r#"
            #[requires(x > 0)]
            #[ensures(result == x)]
            fn identity(x: i32) -> i32 {
                assert!(x == x);
                x
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_no_cheating_clean.rs");
        std::fs::write(&tmp, source).unwrap();
        let findings = scan_file_trusted_constructs(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert!(
            findings.is_empty(),
            "ordinary contracts should not trip no-cheating: {findings:?}"
        );
    }

    /// A `global size_of usize == N` directive line must not change which
    /// functions `scan_file` discovers: it is stripped before parsing. Before
    /// the strip wiring, the directive made the whole file fail to parse, so a
    /// directive file discovered ZERO functions while the same file without the
    /// directive discovered its functions. Part of #2778 arch-width support.
    #[test]
    fn pointer_width_directive_does_not_change_scan_result() {
        let body = "#[trust_vc::verify]\nfn demo(x: u32) -> u32 { x }\n";
        let with = std::env::temp_dir().join("tvc_scan_directive_with.rs");
        let without = std::env::temp_dir().join("tvc_scan_directive_without.rs");
        std::fs::write(&with, format!("global size_of usize == 4;\n{body}")).unwrap();
        std::fs::write(&without, body).unwrap();
        let with_count = scan_file(&with).len();
        let without_count = scan_file(&without).len();
        std::fs::remove_file(&with).ok();
        std::fs::remove_file(&without).ok();
        assert_eq!(
            with_count, without_count,
            "the pointer-width directive must not change which functions are discovered"
        );
    }

    #[test]
    fn test_no_cheating_scan_rejects_trusted_attrs_macros_and_calls() {
        let source = r#"
            #[trust_vc::external_body]
            fn trusted_impl(x: i32) -> i32 { x }

            #[verifier(assume_specification)]
            fn assumed_spec() {}

            fn proof_surface(x: i32) {
                trust_vc::assume!(x > 0);
                assume_by(x > 1);
                admit();
                trust_vc::external_spec! {
                    fn ext(x: i32) -> i32;
                }
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_no_cheating_trusted.rs");
        std::fs::write(&tmp, source).unwrap();
        let findings = scan_file_trusted_constructs(&tmp);
        std::fs::remove_file(&tmp).ok();

        let constructs: Vec<&str> = findings
            .iter()
            .map(|finding| finding.construct.as_str())
            .collect();
        assert!(constructs.contains(&"external_body"), "{findings:?}");
        assert!(constructs.contains(&"assume_specification"), "{findings:?}");
        assert!(constructs.contains(&"assume"), "{findings:?}");
        assert!(constructs.contains(&"assume_by"), "{findings:?}");
        assert!(constructs.contains(&"admit"), "{findings:?}");
        assert!(constructs.contains(&"external_spec"), "{findings:?}");
    }

    /// Verus parity (`test_proof_note_on_assume_with_no_cheating`): a labeled
    /// `assume!` finding carries the user's label text through the
    /// `--no-cheating` channel — "note: {text}" for `proof_note`, the raw
    /// replacement text for `custom_err`.
    #[test]
    fn test_no_cheating_assume_finding_carries_proof_note_label() {
        let source = r#"
            fn caller() {
                #[verifier::proof_note("Statement known to be false")]
                trust_vc::assume!(1 > 2);
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_no_cheating_proof_note.rs");
        std::fs::write(&tmp, source).unwrap();
        let findings = scan_file_trusted_constructs(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert!(
            findings.iter().any(|finding| finding.construct == "assume"
                && finding.detail.contains("note: Statement known to be false")),
            "labeled assume finding must carry the proof_note text: {findings:?}"
        );
    }

    #[test]
    fn test_no_cheating_assume_finding_carries_custom_err_text() {
        let source = r#"
            fn caller() {
                #[verifier::custom_err("Custom assume error")]
                trust_vc::assume!(1 > 2);
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_no_cheating_custom_err.rs");
        std::fs::write(&tmp, source).unwrap();
        let findings = scan_file_trusted_constructs(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert!(
            findings.iter().any(|finding| finding.construct == "assume"
                && finding.detail.contains("Custom assume error")),
            "labeled assume finding must carry the custom_err text: {findings:?}"
        );
    }

    /// Expression-level label inside the macro tokens (the upstream
    /// normalized position) reaches the finding detail too.
    #[test]
    fn test_no_cheating_assume_finding_carries_expr_level_label() {
        let source = r#"
            fn caller() {
                trust_vc::assume!(#[verifier::proof_note("Inner label")] (1 > 2));
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_no_cheating_inner_note.rs");
        std::fs::write(&tmp, source).unwrap();
        let findings = scan_file_trusted_constructs(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert!(
            findings.iter().any(|finding| finding.construct == "assume"
                && finding.detail.contains("note: Inner label")),
            "expression-level label must reach the finding detail: {findings:?}"
        );
    }

    /// Negative control: an unlabeled assume finding's detail is unchanged
    /// (no fabricated note text).
    #[test]
    fn test_no_cheating_assume_finding_without_label_unchanged() {
        let source = r#"
            fn caller() {
                trust_vc::assume!(1 > 2);
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_no_cheating_unlabeled.rs");
        std::fs::write(&tmp, source).unwrap();
        let findings = scan_file_trusted_constructs(&tmp);
        std::fs::remove_file(&tmp).ok();

        let assume = findings
            .iter()
            .find(|finding| finding.construct == "assume")
            .expect("assume finding present");
        assert!(
            !assume.detail.contains("note:"),
            "unlabeled assume must not gain a note: {findings:?}"
        );
    }

    #[test]
    fn test_no_cheating_scan_detects_nested_proof_block_assumption() {
        let source = r#"
            fn proof_block_assumption(x: i32) {
                trust_vc::assert_by!(x == x, {
                    trust_vc::assume!(false);
                });
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_no_cheating_nested.rs");
        std::fs::write(&tmp, source).unwrap();
        let findings = scan_file_trusted_constructs(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert!(
            findings
                .iter()
                .any(|finding| finding.construct == "assume" && finding.detail.contains("nested")),
            "nested proof-block assume should be detected: {findings:?}"
        );
    }

    #[test]
    fn test_no_cheating_scan_flags_via_fn_backed_by_external_body() {
        let source = r#"
            #[trust_vc::via_fn]
            #[trust_vc::external_body]
            fn termination_proof(n: u64) {
                assert!(n == n);
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_no_cheating_via_external.rs");
        std::fs::write(&tmp, source).unwrap();
        let findings = scan_file_trusted_constructs(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert!(
            findings
                .iter()
                .any(|finding| finding.construct == "via_fn_external_body"),
            "via_fn backed by external_body should be called out: {findings:?}"
        );
    }

    #[test]
    fn test_no_cheating_scan_rejects_renamed_trusted_macro_import() {
        let source = r#"
            use trust_vc::assume as ok;

            fn hidden_assumption(x: i32) {
                ok!(x > 0);
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_no_cheating_alias_macro.rs");
        std::fs::write(&tmp, source).unwrap();
        let findings = scan_file_trusted_constructs(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert!(
            findings.iter().any(|finding| {
                finding.construct == "assume" && finding.detail.contains("alias for `assume`")
            }),
            "renamed trusted macro import should be rejected: {findings:?}"
        );
    }

    #[test]
    fn test_no_cheating_scan_rejects_renamed_trusted_attribute_import() {
        let source = r#"
            use trust_vc::external_body as trusted_impl;

            #[trusted_impl]
            fn hidden_external_body(x: i32) -> i32 { x }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_no_cheating_alias_attr.rs");
        std::fs::write(&tmp, source).unwrap();
        let findings = scan_file_trusted_constructs(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert!(
            findings.iter().any(|finding| {
                finding.construct == "external_body"
                    && finding.detail.contains("alias for `external_body`")
            }),
            "renamed trusted attribute import should be rejected: {findings:?}"
        );
    }

    #[test]
    fn test_no_cheating_scan_rejects_macro_forwarding_trusted_ident() {
        let source = r#"
            macro_rules! call {
                ($m:ident) => { $m!(false); }
            }

            fn forwarded_assumption() {
                call!(assume);
            }
        "#;
        let tmp = std::env::temp_dir().join("trust_vc_no_cheating_macro_forward.rs");
        std::fs::write(&tmp, source).unwrap();
        let findings = scan_file_trusted_constructs(&tmp);
        std::fs::remove_file(&tmp).ok();

        assert!(
            findings.iter().any(
                |finding| finding.construct == "assume" && finding.detail.contains("forwarded")
            ),
            "macro forwarding of a trusted identifier should be rejected: {findings:?}"
        );
    }
}
