// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Resolve trust_vc contract attributes written through a `use ... as ...`
//! RENAME back to their canonical `trust_vc::<name>` spelling.
//!
//! # Why this exists
//!
//! Both halves of the source-verification lane recognize a contract attribute
//! by its LAST PATH SEGMENT — `crate::scan`'s `TRUST_VC_ATTRS` decides whether a
//! function is DISCOVERED at all, and
//! [`crate::vc_extraction::attr_extract`]'s clause match decides whether it
//! yields an obligation. A legal Rust rename defeats both at once:
//!
//! ```ignore
//! use trust_vc::ensures as promises;
//!
//! #[promises(result == 42u64)]
//! pub fn liar() -> u64 { 7u64 }
//! ```
//!
//! `promises` is in neither list, so the scan never saw the function, the
//! extractor never saw the contract, and `cargo trust-vc check --json` printed
//! `"functions": []` with an all-zero summary and exit 0 — a clean pass over a
//! file that was never verified. No false proof was emitted, which is exactly
//! what made it dangerous: the failure was INVISIBLE.
//!
//! # The invariant this establishes
//!
//! **An aliased attribute behaves exactly as the canonical spelling does.** The
//! rewrite is a pure renaming performed on the parsed AST, so every downstream
//! pass — discovery, extraction, the unknown-`trust_vc::` clause gate, mode
//! scanning — sees precisely the program the author wrote, spelled the way the
//! toolchain already understands. Nothing is granted that
//! `#[trust_vc::ensures(..)]` would not have granted, and nothing is excused
//! that it would not have excused.
//!
//! # Where it runs (single point, deliberately)
//!
//! [`crate::parse_file_allow_tracked`] — the one parse entry the scanner, the
//! extractor and the mode passes all share. Putting the rewrite anywhere else
//! would re-create the exact defect it fixes: one lane resolving the alias while
//! another silently does not, which is how a discovered function with no visible
//! contract could verify VACUOUSLY. Resolving before either lane looks means the
//! two can never disagree.
//!
//! # Deliberate narrowness
//!
//! * Only `UseTree::Rename` with a genuinely different visible name is rewritten.
//!   A plain `use trust_vc::ensures;` needs no help — the bare `#[ensures(..)]`
//!   already matches by last segment — and rewriting it would newly route names
//!   like `cite` through the `trust_vc::`-namespaced unknown-clause gate,
//!   changing behavior for spellings that work today.
//! * The imported path must mention `trust_vc`, matching the namespace test the
//!   extractor's own gate uses.
//! * `use` bindings are MODULE-SCOPED, so each `mod { .. }` body is resolved
//!   against its OWN bindings and never inherits its parent's. Over-applying a
//!   parent's rename inside a child module would rewrite an attribute the author
//!   never aliased there.
//! * A visible name bound more than once, or bound to two different trust_vc
//!   attributes, is DECLINED rather than guessed. First-binding-wins is how a
//!   different resolver in this tree turned a legal file into a false verify;
//!   an ambiguous rename stays unresolved and is REPORTED, so the function
//!   surfaces as not-analyzed instead of silently taking one arbitrary reading.
//! * Attribute paths with more than one segment (`#[m::promises(..)]`) are left
//!   alone. Those resolve through module paths this pass does not model; they
//!   remain unresolved and are reported by the scan's not-analyzed channel.

use std::collections::BTreeMap;
use syn::spanned::Spanned as _;

/// Attribute names that may be reached through a `use trust_vc::<name> as ..`
/// rename.
///
/// Covers the clause names the contract extractor consumes plus the markers the
/// scanner treats as "this function is a verification target".
/// `cargo-trust-vc`'s `aliasable_attrs_cover_scanner_attrs` test asserts that
/// every scanner attribute is here unless it is deliberately excluded below, so
/// a name added to the scanner and forgotten here fails a test rather than
/// silently losing its alias support.
pub const ALIASABLE_ATTRS: &[&str] = &[
    // Contract clauses — the dangerous ones. These carry proof obligations, and
    // a spelling the extractor does not recognize is a claim that is never
    // checked.
    "requires",
    "ensures",
    "recommends",
    "returns",
    "contract",
    "default_ensures",
    "decreases",
    // Modes and markers that make the scanner treat a function as a target.
    "proof",
    "spec",
    "opaque",
    "inline",
    "rlimit",
    "broadcast",
    "trigger",
    "trait_spec",
    "trait_impl",
];

/// Attribute names deliberately NOT resolved here, and why.
///
/// `external`, `external_body` and `cite` are TRUSTED constructs. The
/// `--no-cheating` scan (`cargo trust_vc check --no-cheating`) already resolves
/// renames of these on its own, and it reports them in the AUTHOR'S spelling —
/// "`trusted_impl` alias for `external_body`" — precisely so a reviewer sees the
/// name that appears in the source. Canonicalizing them here would erase the
/// alias from that diagnostic while adding nothing: unlike a contract clause,
/// these names are not the difference between a claim being checked and a claim
/// being dropped, and an unresolved rename of one still surfaces through the
/// not-analyzed channel rather than vanishing.
pub const NON_ALIASABLE_TRUSTED_ATTRS: &[&str] = &["external", "external_body", "cite"];

/// A rename this pass refused to resolve, and why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclinedAlias {
    /// The visible name the author wrote in the attribute position.
    pub alias: String,
    /// Human-readable justification, surfaced in the not-analyzed report.
    pub reason: String,
}

/// What [`resolve_contract_attr_aliases`] did to a file.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AliasReport {
    /// `(visible name, canonical trust_vc attribute)` pairs actually rewritten.
    pub resolved: Vec<(String, String)>,
    /// Renames left in place because resolving them would have been a guess.
    pub declined: Vec<DeclinedAlias>,
}

impl AliasReport {
    /// True when the file used no trust_vc attribute rename at all.
    pub fn is_empty(&self) -> bool {
        self.resolved.is_empty() && self.declined.is_empty()
    }

    /// The decline recorded for `alias`, if this file declined that name.
    pub fn declined_reason(&self, alias: &str) -> Option<&str> {
        self.declined
            .iter()
            .find(|entry| entry.alias == alias)
            .map(|entry| entry.reason.as_str())
    }
}

/// Rewrite every `use trust_vc::<attr> as <alias>` attribute use in `file` to the
/// canonical `#[trust_vc::<attr>(..)]` spelling, in place.
///
/// Returns what was rewritten and what was declined. A file with no such rename
/// is left byte-for-byte equivalent — the walk mutates nothing.
pub fn resolve_contract_attr_aliases(file: &mut syn::File) -> AliasReport {
    let mut report = AliasReport::default();
    resolve_in_items(&mut file.items, &mut report);
    report
}

/// One module body: collect its own bindings, then rewrite its own items.
fn resolve_in_items(items: &mut [syn::Item], report: &mut AliasReport) {
    let bindings = collect_bindings(items, report);
    for item in items.iter_mut() {
        rewrite_item(item, &bindings, report);
    }
}

/// `visible name -> Some(canonical attribute)` when unambiguous, `None` when the
/// name is bound more than once and must not be guessed at.
type Bindings = BTreeMap<String, Option<String>>;

fn collect_bindings(items: &[syn::Item], report: &mut AliasReport) -> Bindings {
    let mut bindings: Bindings = BTreeMap::new();
    for item in items {
        if let syn::Item::Use(item_use) = item {
            collect_from_use_tree(&mut Vec::new(), &item_use.tree, &mut bindings);
        }
    }
    for (alias, target) in &bindings {
        match target {
            Some(canonical) => report.resolved.push((alias.clone(), canonical.clone())),
            None => report.declined.push(DeclinedAlias {
                alias: alias.clone(),
                reason: format!(
                    "`{alias}` is bound by more than one `use` in this module, so the \
                     trust_vc attribute it names is ambiguous — declining to guess; \
                     spell the contract `#[trust_vc::<clause>(..)]`"
                ),
            }),
        }
    }
    bindings
}

fn collect_from_use_tree(prefix: &mut Vec<String>, tree: &syn::UseTree, bindings: &mut Bindings) {
    match tree {
        syn::UseTree::Path(path) => {
            prefix.push(path.ident.to_string());
            collect_from_use_tree(prefix, &path.tree, bindings);
            prefix.pop();
        }
        syn::UseTree::Group(group) => {
            for tree in &group.items {
                collect_from_use_tree(prefix, tree, bindings);
            }
        }
        syn::UseTree::Rename(rename) => {
            let imported = rename.ident.to_string();
            let visible = rename.rename.to_string();
            // `use trust_vc::ensures as ensures` is not a rename in any sense
            // that matters; the bare name already resolves.
            if visible == imported {
                return;
            }
            // A rename that does NOT come from trust_vc cannot name a contract
            // attribute, and a rename of something that is not an aliasable
            // attribute has no canonical form to rewrite to. Neither is recorded
            // — an unrelated `use std::io::Read as R` must not appear in a
            // contract report.
            if !prefix_names_trust_vc(prefix) || !ALIASABLE_ATTRS.contains(&imported.as_str()) {
                return;
            }
            record_binding(bindings, visible, imported);
        }
        // A plain `use trust_vc::ensures;` needs no rewrite: the bare
        // `#[ensures(..)]` already matches by last segment everywhere.
        syn::UseTree::Name(_) => {}
        // A glob cannot introduce a RENAME, so it cannot hide a contract behind a
        // name the toolchain does not already recognize.
        syn::UseTree::Glob(_) => {}
    }
}

fn record_binding(bindings: &mut Bindings, visible: String, imported: String) {
    match bindings.get(&visible) {
        // Same visible name, same target, written twice: still unambiguous.
        Some(Some(existing)) if *existing == imported => {}
        // Bound already, to something else: refuse to pick one.
        Some(_) => {
            bindings.insert(visible, None);
        }
        None => {
            bindings.insert(visible, Some(imported));
        }
    }
}

/// True when a `use` prefix mentions the `trust_vc` namespace.
///
/// Mirrors `attr_extract::is_trust_vc_namespaced`: any segment may be
/// `trust_vc`, so `trust_vc::ensures`, `::trust_vc::ensures` and a re-export
/// path such as `mycrate::trust_vc::ensures` all qualify, while `std::io::Read`
/// and `crate::helpers::ensures` do not.
fn prefix_names_trust_vc(prefix: &[String]) -> bool {
    prefix.iter().any(|segment| segment == "trust_vc")
}

fn rewrite_item(item: &mut syn::Item, bindings: &Bindings, report: &mut AliasReport) {
    match item {
        syn::Item::Fn(item_fn) => rewrite_attrs(&mut item_fn.attrs, bindings),
        syn::Item::Impl(item_impl) => {
            rewrite_attrs(&mut item_impl.attrs, bindings);
            for impl_item in &mut item_impl.items {
                if let syn::ImplItem::Fn(method) = impl_item {
                    rewrite_attrs(&mut method.attrs, bindings);
                }
            }
        }
        syn::Item::Trait(item_trait) => {
            rewrite_attrs(&mut item_trait.attrs, bindings);
            for trait_item in &mut item_trait.items {
                if let syn::TraitItem::Fn(method) = trait_item {
                    rewrite_attrs(&mut method.attrs, bindings);
                }
            }
        }
        syn::Item::Mod(item_mod) => {
            rewrite_attrs(&mut item_mod.attrs, bindings);
            // A nested module does NOT inherit this module's `use` bindings, so
            // it is resolved against its own — never against `bindings`.
            if let Some((_, items)) = &mut item_mod.content {
                resolve_in_items(items, report);
            }
        }
        _ => {}
    }
}

fn rewrite_attrs(attrs: &mut [syn::Attribute], bindings: &Bindings) {
    for attr in attrs.iter_mut() {
        let Some(canonical) = canonical_for_attr(attr, bindings) else {
            continue;
        };
        let path = attr.path();
        let span = path.span();
        let canonical_path = canonical_trust_vc_path(&canonical, span);
        match &mut attr.meta {
            syn::Meta::Path(meta_path) => *meta_path = canonical_path,
            syn::Meta::List(meta_list) => meta_list.path = canonical_path,
            syn::Meta::NameValue(meta_name_value) => meta_name_value.path = canonical_path,
        }
    }
}

/// The canonical attribute name an attribute path should be rewritten to, if any.
///
/// Only a SINGLE-segment path can be a renamed import in this module's scope; a
/// multi-segment path already names where it comes from and is left alone.
fn canonical_for_attr(attr: &syn::Attribute, bindings: &Bindings) -> Option<String> {
    let path = attr.path();
    if path.leading_colon.is_some() || path.segments.len() != 1 {
        return None;
    }
    let name = path.segments.first()?.ident.to_string();
    bindings.get(&name)?.clone()
}

fn canonical_trust_vc_path(name: &str, span: proc_macro2::Span) -> syn::Path {
    let mut segments = syn::punctuated::Punctuated::new();
    segments.push(syn::PathSegment {
        ident: syn::Ident::new("trust_vc", span),
        arguments: syn::PathArguments::None,
    });
    segments.push(syn::PathSegment {
        ident: syn::Ident::new(name, span),
        arguments: syn::PathArguments::None,
    });
    syn::Path {
        leading_colon: None,
        segments,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::ToTokens as _;

    /// Resolve `source` and return the rendered ATTRIBUTE PATHS on every `fn`
    /// item, plus the report.
    ///
    /// Deliberately not the whole file: a fixture necessarily contains the
    /// `use trust_vc::ensures as post;` line it is testing, and rendering the
    /// file would make every "was it rewritten?" assertion match that `use`
    /// item instead of the attribute. Looking only at attribute paths asks the
    /// question the pass actually answers.
    fn resolve(source: &str) -> (Vec<String>, AliasReport) {
        let mut file: syn::File = syn::parse_file(source).expect("fixture parses");
        let report = resolve_contract_attr_aliases(&mut file);
        let mut paths = Vec::new();
        collect_fn_attr_paths(&file.items, &mut paths);
        (paths, report)
    }

    fn collect_fn_attr_paths(items: &[syn::Item], out: &mut Vec<String>) {
        fn render(attrs: &[syn::Attribute], out: &mut Vec<String>) {
            for attr in attrs {
                out.push(attr.path().to_token_stream().to_string());
            }
        }
        for item in items {
            match item {
                syn::Item::Fn(item_fn) => render(&item_fn.attrs, out),
                syn::Item::Impl(item_impl) => {
                    for impl_item in &item_impl.items {
                        if let syn::ImplItem::Fn(method) = impl_item {
                            render(&method.attrs, out);
                        }
                    }
                }
                syn::Item::Trait(item_trait) => {
                    for trait_item in &item_trait.items {
                        if let syn::TraitItem::Fn(method) = trait_item {
                            render(&method.attrs, out);
                        }
                    }
                }
                syn::Item::Mod(item_mod) => {
                    if let Some((_, items)) = &item_mod.content {
                        collect_fn_attr_paths(items, out);
                    }
                }
                _ => {}
            }
        }
    }

    fn has_attr(paths: &[String], needle: &str) -> bool {
        paths.iter().any(|path| path == needle)
    }

    #[test]
    fn a_renamed_ensures_becomes_the_canonical_spelling() {
        let (attrs, report) = resolve(
            "use trust_vc::ensures as promises;\n\
             #[promises(result == 42u64)]\n\
             pub fn liar() -> u64 { 7u64 }\n",
        );
        assert!(
            has_attr(&attrs, "trust_vc :: ensures"),
            "alias was not rewritten: {attrs:?}"
        );
        assert_eq!(
            report.resolved,
            vec![("promises".to_string(), "ensures".to_string())]
        );
        assert!(report.declined.is_empty());
    }

    #[test]
    fn a_grouped_rename_resolves_every_member() {
        let (attrs, report) = resolve(
            "use trust_vc::{requires as pre, ensures as post};\n\
             #[pre(x > 0)]\n\
             #[post(result > 0)]\n\
             pub fn f(x: u64) -> u64 { x }\n",
        );
        assert!(has_attr(&attrs, "trust_vc :: requires"), "{attrs:?}");
        assert!(has_attr(&attrs, "trust_vc :: ensures"), "{attrs:?}");
        assert_eq!(report.resolved.len(), 2);
    }

    #[test]
    fn a_pub_use_rename_resolves() {
        let (attrs, _) = resolve(
            "pub use trust_vc::ensures as post;\n\
             #[post(result == 1u64)]\n\
             pub fn f() -> u64 { 1u64 }\n",
        );
        assert!(has_attr(&attrs, "trust_vc :: ensures"), "{attrs:?}");
    }

    #[test]
    fn an_impl_method_attribute_resolves() {
        let (attrs, _) = resolve(
            "use trust_vc::ensures as post;\n\
             struct S;\n\
             impl S { #[post(result == 1u64)] fn f(&self) -> u64 { 1u64 } }\n",
        );
        assert!(has_attr(&attrs, "trust_vc :: ensures"), "{attrs:?}");
    }

    #[test]
    fn a_rename_from_another_crate_is_left_alone() {
        let (attrs, report) = resolve(
            "use other::ensures as post;\n\
             #[post(result == 1u64)]\n\
             pub fn f() -> u64 { 1u64 }\n",
        );
        assert_eq!(attrs, vec!["post".to_string()], "{attrs:?}");
        assert!(report.is_empty());
    }

    #[test]
    fn a_plain_import_is_not_rewritten() {
        // The bare `#[ensures(..)]` already resolves by last segment; rewriting
        // it would change which gate unknown names fall into.
        let (attrs, report) = resolve(
            "use trust_vc::ensures;\n\
             #[ensures(result == 1u64)]\n\
             pub fn f() -> u64 { 1u64 }\n",
        );
        assert_eq!(attrs, vec!["ensures".to_string()], "{attrs:?}");
        assert!(report.is_empty());
    }

    #[test]
    fn a_nested_module_does_not_inherit_the_outer_rename() {
        let (attrs, _) = resolve(
            "use trust_vc::ensures as post;\n\
             mod inner {\n\
                 #[post(result == 1u64)]\n\
                 pub fn f() -> u64 { 1u64 }\n\
             }\n",
        );
        assert_eq!(
            attrs,
            vec!["post".to_string()],
            "outer rename leaked into a nested module"
        );
    }

    #[test]
    fn a_nested_module_resolves_its_own_rename() {
        let (attrs, report) = resolve(
            "mod inner {\n\
                 use trust_vc::ensures as post;\n\
                 #[post(result == 1u64)]\n\
                 pub fn f() -> u64 { 1u64 }\n\
             }\n",
        );
        assert!(has_attr(&attrs, "trust_vc :: ensures"), "{attrs:?}");
        assert_eq!(report.resolved.len(), 1);
    }

    #[test]
    fn an_ambiguous_rename_is_declined_not_guessed() {
        let (attrs, report) = resolve(
            "use trust_vc::ensures as post;\n\
             use trust_vc::requires as post;\n\
             #[post(result == 1u64)]\n\
             pub fn f() -> u64 { 1u64 }\n",
        );
        assert_eq!(
            attrs,
            vec!["post".to_string()],
            "an ambiguous rename was resolved anyway"
        );
        assert!(report.resolved.is_empty());
        assert_eq!(report.declined.len(), 1);
        assert_eq!(report.declined[0].alias, "post");
        assert!(report.declined_reason("post").is_some());
    }

    #[test]
    fn a_multi_segment_attribute_path_is_left_alone() {
        let (attrs, _) = resolve(
            "use trust_vc::ensures as post;\n\
             #[m::post(result == 1u64)]\n\
             pub fn f() -> u64 { 1u64 }\n",
        );
        assert_eq!(attrs, vec!["m :: post".to_string()], "{attrs:?}");
    }

    /// A renamed TRUSTED construct is left in the author's spelling on purpose;
    /// the `--no-cheating` lane resolves and reports it itself.
    #[test]
    fn a_renamed_trusted_construct_is_left_for_the_no_cheating_lane() {
        let (attrs, report) = resolve(
            "use trust_vc::external_body as trusted_impl;\n\
             #[trusted_impl]\n\
             fn hidden(x: i32) -> i32 { x }\n",
        );
        assert_eq!(attrs, vec!["trusted_impl".to_string()], "{attrs:?}");
        assert!(report.is_empty());
    }

    #[test]
    fn the_two_attribute_lists_do_not_overlap() {
        for name in NON_ALIASABLE_TRUSTED_ATTRS {
            assert!(
                !ALIASABLE_ATTRS.contains(name),
                "`{name}` is both aliasable and exempted"
            );
        }
    }

    #[test]
    fn a_file_without_renames_is_untouched() {
        let source = "#[trust_vc::ensures(result == 1u64)]\npub fn f() -> u64 { 1u64 }\n";
        let mut file: syn::File = syn::parse_file(source).expect("parses");
        let before = file.to_token_stream().to_string();
        let report = resolve_contract_attr_aliases(&mut file);
        assert_eq!(before, file.to_token_stream().to_string());
        assert!(report.is_empty());
    }

    #[test]
    fn the_rewrite_preserves_the_attribute_line() {
        let mut file: syn::File = syn::parse_file(
            "use trust_vc::ensures as post;\n\n\n#[post(result == 1u64)]\npub fn f() -> u64 { 1u64 }\n",
        )
        .expect("parses");
        resolve_contract_attr_aliases(&mut file);
        let syn::Item::Fn(item_fn) = &file.items[1] else {
            panic!("expected a fn item");
        };
        let line = item_fn.attrs[0]
            .path()
            .segments
            .last()
            .expect("segment")
            .ident
            .span()
            .start()
            .line;
        assert_eq!(line, 4, "rewritten attribute lost its source line");
    }
}
