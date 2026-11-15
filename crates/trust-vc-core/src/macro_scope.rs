//! FILE-scope resolution for the macro NAMES trust-vc's lanes treat specially.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Every lane that gives a macro a meaning — `assume!` becomes a spec
//! ASSUMPTION, `matches!` is rewritten to its `match` expansion, `assert!`
//! becomes an obligation — identified that macro by its BARE NAME, or by the
//! LAST segment of its path with every qualifier discarded. Neither is
//! resolution. A `macro_rules! assume` declared in the file textually shadows
//! the trust-vc macro for every later call site, and `m::assume!` names a macro
//! in `m` that has nothing to do with trust-vc; both were read as the trust-vc
//! macro and answered confidently.
//!
//! Two of those were CARDINAL false verifies, in the worst possible pairing:
//!
//! ```ignore
//! macro_rules! assume { ($e:expr) => {}; }          // a NO-OP
//! assume!(x == 0u64);                               // consumed as a PREMISE
//! trust_vc::assert!(x <= 255u64);                   // VERIFIED — it is false
//!
//! macro_rules! matches { ($e:expr, $p:pat) => { false }; }
//! trust_vc::assert!(matches!(y, 7u8));              // VERIFIED — it is false
//! trust_vc::assert!(!matches!(y, 7u8));             // refuted  — it is true
//! ```
//!
//! Both directions wrong at once, on legal single-file Rust, through the
//! production CLI. See `macro_shadow_soundness.rs` for the cardinal tests.
//!
//! # What this module decides
//!
//! One question, for one invocation: **does this path name the well-known macro
//! its last segment is spelled like?** [`MacroPathScopes::resolves_to_well_known`]
//! answers it, and answers `false` for everything it cannot settle from the file
//! alone. `false` means the caller must fail closed — never "resolve it
//! innermost-wins", because naming the WRONG declaration is the false-verify
//! direction.
//!
//! # How the answer is enforced
//!
//! [`quarantine_shadowed_spec_macros`] rewrites the offending macro NAME to
//! [`QUARANTINED_MACRO_NAME`], a reserved ident no lane recognises, so every
//! name-keyed lane — the body extractor's macro match, the `matches!` desugar,
//! the contract-attribute re-parsers — fails closed without any of them being
//! taught about scopes. The rewrite runs over the function's whole TOKEN
//! STREAM rather than an arm per syntactic position, because the two nested
//! reproducers (`trust_vc::proof_block!({ assume!(..) })` and
//! `trust_vc::assert_by!(c, { assume!(..) })`) live inside token streams that
//! no `syn` visitor descends into. Enumerating the positions a macro can be
//! written in is exactly the shape that left the last four holes open.

use std::collections::BTreeSet;

use proc_macro2::{Group, Ident, Spacing, TokenStream, TokenTree};
use quote::ToTokens;
use syn::visit::Visit;
use syn::{File, ItemFn};

/// Crate roots whose macros a name-keyed trust-vc lane may treat as the
/// well-known macro of that name.
///
/// This is an allowlist of ROOTS, not of spellings: `trust_vc::assume!`,
/// `trust_vc::macros::assume!` and `::trust_vc::assume!` all resolve, while
/// `m::assume!` — for ANY other `m` — does not. `trust_mc` is here because the
/// proc-macro lane emits `::trust_mc::{assert,assume}!` for the runtime
/// obligations; `std`/`core` because `std::matches!` IS the std macro.
///
/// A root is only believed when the file has not REBOUND it — `mod trust_vc {}`
/// or `use x as core;` makes the root name something else entirely, and
/// [`MacroScopeIndex::rebound_roots`] takes it back out.
///
/// `trust_vc_types` and `vstd` are here for the ghost-collection lane: the
/// ported corpus writes `trust_vc_types::seq!` 284 times, `trust_vc_types::map!`
/// 30 and `vstd::seq!` 3. `crate` and `self` are NOT roots — they are handled by
/// [`MacroPathScopes::resolves_to_well_known`] as a relative path back into this
/// file, which is strictly more precise than an allowlist entry.
const WELL_KNOWN_MACRO_ROOTS: &[&str] = &[
    "trust_vc",
    "trust_vc_types",
    "trust_mc",
    "vstd",
    "std",
    "core",
];

/// The reserved macro name every name-keyed lane fails closed on.
///
/// It is not in [`SPEC_MACRO_NAMES`] and matches no arm of the body
/// extractor's macro dispatch, so it lands on that dispatch's
/// `_ => Err(unsupported_macro_error(mac))`. Pinned in all six positions a
/// quarantined macro can end up in by `macro_shadow_soundness.rs`.
pub(crate) const QUARANTINED_MACRO_NAME: &str = "__trust_vc_shadowed_macro";

/// Every macro NAME a name-keyed trust-vc lane gives a MEANING to.
///
/// This is the single canonical list. `is_supported_body_macro_name` in
/// `vc_extraction::body_extract` is derived from it (see
/// [`is_body_lane_supported_macro_name`]) rather than repeating it, so a name
/// that is dispatched but missing here stops being routed at all — a loud
/// failure — instead of silently escaping the scope check.
///
/// Membership here does NOT mean "trust-vc supports it". It means "trust-vc
/// decides what it means from its name", which is precisely the set whose
/// resolution has to be checked.
pub(crate) const SPEC_MACRO_NAMES: &[&str] = &[
    "assert",
    "trust_vc_assert",
    "assume",
    "trust_vc_assume",
    "reveal",
    "trust_vc_reveal",
    "hide",
    "trust_vc_hide",
    "broadcast_use",
    "trust_vc_broadcast_use",
    "invariant",
    "trust_vc_invariant",
    "invariant_except_break",
    "trust_vc_invariant_except_break",
    "loop_ensures",
    "trust_vc_loop_ensures",
    "loop_decreases",
    "trust_vc_loop_decreases",
    "assert_eq",
    "assert_ne",
    "assert_seqs_equal",
    "calc",
    "assert_forall_by",
    "assert_by_nonlinear",
    "assert_by_bit_vector",
    "assert_by_compute",
    "assert_by_contradiction",
    "assert_by",
    "trust_vc_assert_by",
    "debug_assert",
    "debug_assert_eq",
    "debug_assert_ne",
    "proof_block",
    "trust_vc_proof_block",
    "matches",
    // The EXPRESSION-macro lane (`is_supported_expression_macro_name`), which
    // keys by bare name exactly as the statement lane did. Two of these were
    // measured false verifies of their own: a `macro_rules! seq` returning an
    // EMPTY sequence still had `seq![1,2,3].len() == 3` VERIFIED, and a
    // `macro_rules! equal` returning `false` still had `equal!(x, x)` VERIFIED.
    "choose",
    "seq",
    "map",
    "set",
    "vec",
    "ext_eq",
    "ext_ne",
    "strict_eq",
    "equal",
];

/// The names the body lane's `is_supported_body_macro_name` deliberately
/// EXCLUDES: `assert_by`/`proof_block` are dispatched by
/// `parse_assertion_obligations` but are not "supported body macros" for the
/// purposes of the statement-position gate; `matches` is a source-level desugar
/// that has been rewritten away before the body lane sees it; and the
/// expression-macro lane's names belong to `is_supported_expression_macro_name`,
/// a different dispatch.
const BODY_LANE_EXCLUDED: &[&str] = &[
    "assert_by",
    "trust_vc_assert_by",
    "proof_block",
    "trust_vc_proof_block",
    "matches",
    "choose",
    "seq",
    "map",
    "set",
    "vec",
    "ext_eq",
    "ext_ne",
    "strict_eq",
    "equal",
];

/// The body lane's view of [`SPEC_MACRO_NAMES`].
pub(crate) fn is_body_lane_supported_macro_name(name: &str) -> bool {
    SPEC_MACRO_NAMES.contains(&name) && !BODY_LANE_EXCLUDED.contains(&name)
}

/// Everything one walk over a file records about what its macro NAMES are bound
/// to.
///
/// Built only by [`MacroScopeIndex::from_file`] and destructured exhaustively in
/// [`MacroPathScopes::resolves_to_well_known`], so a field added here cannot
/// compile until the resolver decides in writing what it means.
#[derive(Default)]
struct MacroScopeIndex {
    /// `(module, name)` for every macro NAME this file binds to something that
    /// is NOT the well-known macro of that name: a `macro_rules! name`, a
    /// `use other::thing as name`, a `use other::name`.
    ///
    /// A `use trust_vc::assume;` is deliberately absent — it binds `assume` to
    /// the macro trust-vc means, so it is not a shadow. That is why this is
    /// keyed on where the binding POINTS, not merely on the fact that a binding
    /// exists.
    shadowed: BTreeSet<(Vec<String>, String)>,
    /// Names whose binding escapes its declaring module (`#[macro_export]`, or
    /// a `macro_rules!` inside a `#[macro_use] mod`). Their scope is not
    /// decidable from the file alone, so they shadow EVERY module.
    shadowed_everywhere: BTreeSet<String>,
    /// Path ROOTS the file rebinds: `mod std { .. }`, `use x as trust_vc;`,
    /// `extern crate x as core;`. A rebound root is not the crate it is spelled
    /// like, so [`WELL_KNOWN_MACRO_ROOTS`] must not believe it. Applied
    /// file-wide — a rebinding's exact visibility is not worth guessing when
    /// guessing wrong is a false verify.
    rebound_roots: BTreeSet<String>,
}

impl MacroScopeIndex {
    fn from_file(file: &File) -> Self {
        let mut collector = ScopeCollector {
            index: MacroScopeIndex::default(),
            module: Vec::new(),
            macro_use_depth: 0usize,
        };
        collector.visit_file(file);
        collector.index
    }
}

/// Walks the file recording macro bindings.
///
/// A `syn::visit::Visit` walk rather than an arm per container on purpose: item
/// containers are not just `File::items` and `ItemMod::content` — a
/// `macro_rules!` or a `use` is legal inside a function body, inside a nested
/// block, inside an `impl`, inside a `const` initialiser block. Enumerating
/// them is what left the const registry open. `Visit` descends into all of them
/// for free; only `ItemMod` needs an override, to track the module path.
///
/// Items declared inside a function body are recorded against their ENCLOSING
/// MODULE. That over-approximates their scope (they are only visible inside
/// that body), which is the fail-closed direction, and it costs nothing: no
/// corpus file declares any of [`SPEC_MACRO_NAMES`] at all.
struct ScopeCollector {
    index: MacroScopeIndex,
    module: Vec<String>,
    macro_use_depth: usize,
}

impl ScopeCollector {
    fn shadow(&mut self, name: String) {
        if self.macro_use_depth > 0 {
            self.index.shadowed_everywhere.insert(name);
        } else {
            self.index.shadowed.insert((self.module.clone(), name));
        }
    }

    /// Record one `use` leaf: `bound` is the name it puts in scope, `root` the
    /// first segment of the path it points at, `leaf` the final segment.
    fn record_use_leaf(&mut self, root: &str, leaf: &str, bound: &str) {
        // `use x as trust_vc;` / `use x::trust_vc;` makes the ROOT ident mean
        // something the allowlist must stop believing.
        if WELL_KNOWN_MACRO_ROOTS.contains(&bound) && bound != root {
            self.index.rebound_roots.insert(bound.to_string());
        }
        // A binding that points into a well-known root AND keeps the name is
        // the well-known macro itself (`use trust_vc::{assume, invariant};`) —
        // not a shadow. Anything else takes the name over, INCLUDING
        // `use trust_vc::hide as assume;`, which binds `assume` to a different
        // macro of trust-vc's own.
        let is_well_known_reexport = WELL_KNOWN_MACRO_ROOTS.contains(&root) && leaf == bound;
        if !is_well_known_reexport {
            self.shadow(bound.to_string());
        }
    }

    fn collect_use_tree(&mut self, tree: &syn::UseTree, root: Option<String>) {
        match tree {
            syn::UseTree::Path(path) => {
                let ident = path.ident.to_string();
                let root = root.or(Some(ident));
                self.collect_use_tree(&path.tree, root);
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    self.collect_use_tree(item, root.clone());
                }
            }
            syn::UseTree::Name(name) => {
                let leaf = name.ident.to_string();
                let root = root.unwrap_or_else(|| leaf.clone());
                self.record_use_leaf(&root, &leaf, &leaf);
            }
            syn::UseTree::Rename(rename) => {
                let leaf = rename.ident.to_string();
                let bound = rename.rename.to_string();
                let root = root.unwrap_or_else(|| leaf.clone());
                self.record_use_leaf(&root, &leaf, &bound);
            }
            // A glob can bind a name this file never spells. It is NOT treated
            // as a shadow: `use vstd::prelude::*;` appears throughout the
            // corpus, and every external crate is already outside what a
            // single-file source pass can resolve — declining on a glob would
            // decline essentially every file without closing anything the file
            // itself makes visible. Recorded here as the one deliberate
            // residual of this pass.
            syn::UseTree::Glob(_) => {}
        }
    }
}

/// The name bound by a declarative macro 2.0 item, read from the token stream
/// syn hands back as `Item::Verbatim`.
///
/// The item's header is `[attrs] [vis] macro NAME …`, so the ident after the
/// `macro` keyword is the binding. `macro_rules` is a different ident and is
/// handled by [`ScopeCollector::visit_item_macro`].
fn verbatim_decl_macro_name(tokens: &TokenStream) -> Option<String> {
    let trees: Vec<TokenTree> = tokens.clone().into_iter().collect();
    trees.iter().enumerate().find_map(|(index, tree)| {
        let TokenTree::Ident(keyword) = tree else {
            return None;
        };
        if keyword != "macro" {
            return None;
        }
        match trees.get(index + 1) {
            Some(TokenTree::Ident(name)) => Some(name.to_string()),
            _ => None,
        }
    })
}

fn has_attr(attrs: &[syn::Attribute], name: &str) -> bool {
    attrs.iter().any(|attr| attr.path().is_ident(name))
}

impl<'ast> Visit<'ast> for ScopeCollector {
    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        let macro_use = has_attr(&item.attrs, "macro_use");
        if WELL_KNOWN_MACRO_ROOTS.contains(&item.ident.to_string().as_str()) {
            self.index.rebound_roots.insert(item.ident.to_string());
        }
        self.module.push(item.ident.to_string());
        if macro_use {
            self.macro_use_depth += 1;
        }
        syn::visit::visit_item_mod(self, item);
        if macro_use {
            self.macro_use_depth -= 1;
        }
        self.module.pop();
    }

    fn visit_item_macro(&mut self, item: &'ast syn::ItemMacro) {
        if let Some(ident) = &item.ident {
            let exported = has_attr(&item.attrs, "macro_export");
            let name = ident.to_string();
            if exported {
                self.index.shadowed_everywhere.insert(name);
            } else {
                self.shadow(name);
            }
        }
        syn::visit::visit_item_macro(self, item);
    }

    fn visit_item(&mut self, item: &'ast syn::Item) {
        // A declarative macro 2.0 (`pub macro assume($e:expr) { .. }`) is not a
        // node syn 2 models — it arrives as `Item::Verbatim`. It binds the name
        // just as `macro_rules!` does, and left unread it was a third
        // reproducer of the same false verify.
        if let syn::Item::Verbatim(tokens) = item {
            if let Some(name) = verbatim_decl_macro_name(tokens) {
                self.shadow(name);
            }
        }
        syn::visit::visit_item(self, item);
    }

    fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
        self.collect_use_tree(&item.tree, None);
        syn::visit::visit_item_use(self, item);
    }

    fn visit_item_extern_crate(&mut self, item: &'ast syn::ItemExternCrate) {
        if let Some((_, rename)) = &item.rename {
            let bound = rename.to_string();
            if WELL_KNOWN_MACRO_ROOTS.contains(&bound.as_str()) && item.ident != bound {
                self.index.rebound_roots.insert(bound);
            }
        }
        syn::visit::visit_item_extern_crate(self, item);
    }
}

/// Resolution of a macro path written at one use site.
struct MacroPathScopes<'a> {
    /// Inline-module path of the function being checked. `None` means the
    /// function's enclosing module could not be identified; the resolver then
    /// takes a name shadowed in ANY module to be shadowed here, which is the
    /// fail-closed direction and is bounded to names the file actually binds.
    use_site_module: Option<&'a [String]>,
    index: &'a MacroScopeIndex,
}

impl MacroPathScopes<'_> {
    /// Does `root::…::name!`, written at this use site, name the WELL-KNOWN
    /// macro spelled `name`?
    ///
    /// `root` is `None` for an unqualified invocation. Every case this cannot
    /// settle from the file alone answers `false`.
    fn resolves_to_well_known(&self, root: Option<&str>, name: &str) -> bool {
        // Exhaustive destructure — see the type docs.
        let MacroPathScopes {
            use_site_module,
            index,
        } = self;
        let MacroScopeIndex {
            shadowed,
            shadowed_everywhere,
            rebound_roots,
        } = index;

        if shadowed_everywhere.contains(name) {
            return false;
        }
        // `crate::` and `self::` are not crate roots — they point back INTO this
        // file, so they are decided by the same shadow check the unqualified
        // spelling gets, at the crate root and at the use site respectively.
        // That is strictly more precise than adding them to the root allowlist,
        // which would have let a file's OWN `macro_rules! assume` be reached as
        // `crate::assume!` and believed. `super::` is not resolvable from a
        // single file and is declined rather than guessed.
        let relative_module: Option<&[String]> = match root {
            Some("crate") => Some(&[]),
            Some("self") => match use_site_module {
                Some(module) => Some(module),
                None => return false,
            },
            Some("super") => return false,
            _ => None,
        };
        if let Some(module) = relative_module {
            return !shadowed.contains(&(module.to_vec(), name.to_string()));
        }
        match root {
            // Qualified: the ROOT decides, and only a root the file has not
            // rebound. `m::assume!` never resolves, whatever `m` holds.
            Some(root) => WELL_KNOWN_MACRO_ROOTS.contains(&root) && !rebound_roots.contains(root),
            // Unqualified: the well-known macro, unless this file binds the
            // name to something else where the use site can see it.
            None => match use_site_module {
                Some(module) => !shadowed.contains(&(module.to_vec(), name.to_string())),
                None => !shadowed.iter().any(|(_, bound)| bound == name),
            },
        }
    }
}

/// The macro bindings of one file, for asking whether a macro path written
/// anywhere in it names the well-known macro it is spelled like.
pub(crate) struct FileMacroScopes {
    index: MacroScopeIndex,
}

impl FileMacroScopes {
    pub(crate) fn from_file(file: &File) -> Self {
        Self {
            index: MacroScopeIndex::from_file(file),
        }
    }

    /// Does `root::…::name!` name the well-known macro spelled `name`, at
    /// whatever use site of the file it is written? A name the file binds to
    /// something else in any module does not.
    pub(crate) fn names_well_known(&self, root: Option<&str>, name: &str) -> bool {
        MacroPathScopes {
            use_site_module: None,
            index: &self.index,
        }
        .resolves_to_well_known(root, name)
    }
}

/// Is `trees[index]` an ident that begins a macro invocation `NAME!(..)`?
///
/// Rust's token grammar makes this exact: an ident followed by an ALONE `!`
/// followed by a delimited group is a macro call and nothing else. `a != b`
/// carries a JOINT `!` (it is glued to the `=`), and `!(a)` has no ident
/// before the `!`.
fn begins_macro_invocation(trees: &[TokenTree], index: usize) -> bool {
    let Some(TokenTree::Punct(bang)) = trees.get(index + 1) else {
        return false;
    };
    if bang.as_char() != '!' || bang.spacing() != Spacing::Alone {
        return false;
    }
    matches!(trees.get(index + 2), Some(TokenTree::Group(_)))
}

/// The ROOT segment of the path an invocation ident is qualified by, read from
/// the tokens already emitted before it.
///
/// Walks back over `IDENT :: ` groups: `a::b::assume!` answers `Some("a")`,
/// `assume!` answers `None`. Anything that is not that shape (a `>` from a
/// qualified self type, a `.` from a field access) stops the walk and answers
/// with whatever root it had reached — `None` if it reached none, which routes
/// to the unqualified rule and its shadow check.
fn path_root_before(emitted: &[TokenTree]) -> Option<String> {
    let mut end = emitted.len();
    let mut root = None;
    while end >= 3 {
        let (TokenTree::Punct(second), TokenTree::Punct(first)) =
            (&emitted[end - 2], &emitted[end - 1])
        else {
            break;
        };
        if second.as_char() != ':' || first.as_char() != ':' {
            break;
        }
        let TokenTree::Ident(ident) = &emitted[end - 3] else {
            break;
        };
        root = Some(ident.to_string());
        end -= 3;
    }
    root
}

/// Rewrite every special-macro invocation in `tokens` whose path does not
/// resolve to the well-known macro into [`QUARANTINED_MACRO_NAME`].
fn quarantine_tokens(
    tokens: TokenStream,
    scopes: &MacroPathScopes<'_>,
    changed: &mut bool,
) -> TokenStream {
    let trees: Vec<TokenTree> = tokens.into_iter().collect();
    let mut emitted: Vec<TokenTree> = Vec::with_capacity(trees.len());
    for (index, tree) in trees.iter().enumerate() {
        match tree {
            TokenTree::Group(group) => {
                let inner = quarantine_tokens(group.stream(), scopes, changed);
                let mut rebuilt = Group::new(group.delimiter(), inner);
                rebuilt.set_span(group.span());
                emitted.push(TokenTree::Group(rebuilt));
            }
            TokenTree::Ident(ident) => {
                let name = ident.to_string();
                if SPEC_MACRO_NAMES.contains(&name.as_str())
                    && begins_macro_invocation(&trees, index)
                    && !scopes.resolves_to_well_known(path_root_before(&emitted).as_deref(), &name)
                {
                    emitted.push(TokenTree::Ident(Ident::new(
                        QUARANTINED_MACRO_NAME,
                        ident.span(),
                    )));
                    *changed = true;
                    continue;
                }
                emitted.push(tree.clone());
            }
            other => emitted.push(other.clone()),
        }
    }
    emitted.into_iter().collect()
}

/// Quarantine every macro invocation in `func` that a name-keyed lane would
/// give a trust-vc meaning to but that this file does not actually bind to the
/// well-known macro.
///
/// Returns `Some(rewritten)` only when something was quarantined, so a function
/// with no shadowed or foreign-qualified special macro — which is every
/// function in the corpus — is handed back untouched, spans and all.
///
/// `file` is `None` on the proc-macro lane, where there is no file to resolve
/// against and the invocation is the trust-vc macro by construction (it is
/// trust-vc's own expansion that produced it).
pub(crate) fn quarantine_shadowed_spec_macros(
    func: &ItemFn,
    file: Option<&File>,
    use_site_module: Option<&[String]>,
) -> Option<ItemFn> {
    let file = file?;
    let index = MacroScopeIndex::from_file(file);
    let scopes = MacroPathScopes {
        use_site_module,
        index: &index,
    };
    let mut changed = false;
    let rewritten = quarantine_tokens(func.to_token_stream(), &scopes, &mut changed);
    if !changed {
        return None;
    }
    syn::parse2::<ItemFn>(rewritten).ok()
}

/// How an ITEM-position invocation of `state_machine!` /
/// `tokenized_state_machine!` resolves (D1a).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ItemMacroResolution {
    /// `trust_vc::NAME!` / `::trust_vc::NAME!` with the `trust_vc` root not
    /// rebound anywhere in the file.
    TrustVc,
    /// A bare `NAME!` bound by a file-local `macro_rules!` that is textually in
    /// scope (declared earlier in this item list or an enclosing one, or
    /// `#[macro_export]`/`#[macro_use]`-escaped), with no `use` in the same
    /// item list binding the name. HEAD behaviour: left untouched.
    LocalMacroRules,
    /// Everything else: a bare name bound by an import or by nothing, a
    /// foreign qualifier, a rebound `trust_vc` root.
    Other,
}

fn item_list_binds_by_use(items: &[syn::Item], name: &str) -> bool {
    fn tree_binds(tree: &syn::UseTree, name: &str) -> bool {
        match tree {
            syn::UseTree::Path(p) => tree_binds(&p.tree, name),
            syn::UseTree::Name(n) => n.ident == name,
            syn::UseTree::Rename(r) => r.rename == name,
            syn::UseTree::Group(g) => g.items.iter().any(|t| tree_binds(t, name)),
            syn::UseTree::Glob(_) => false,
        }
    }
    items.iter().any(|item| match item {
        syn::Item::Use(u) => tree_binds(&u.tree, name),
        _ => false,
    })
}

fn is_macro_rules_named(item: &syn::Item, name: &str) -> bool {
    matches!(item, syn::Item::Macro(m)
        if m.mac.path.is_ident("macro_rules")
            && m.ident.as_ref().is_some_and(|ident| ident == name))
}

fn file_exports_macro(items: &[syn::Item], name: &str, in_macro_use: bool) -> bool {
    items.iter().any(|item| match item {
        syn::Item::Macro(m) if is_macro_rules_named(item, name) => {
            in_macro_use || has_attr(&m.attrs, "macro_export")
        }
        syn::Item::Mod(module) => module.content.as_ref().is_some_and(|(_, inner)| {
            file_exports_macro(
                inner,
                name,
                in_macro_use || has_attr(&module.attrs, "macro_use"),
            )
        }),
        _ => false,
    })
}

/// Resolve the item-macro invocation at `path_to_item` (indices through
/// nested inline modules, the last one naming the macro item itself).
pub(crate) fn resolve_item_macro(file: &File, path_to_item: &[usize]) -> ItemMacroResolution {
    let mut items: &[syn::Item] = &file.items;
    let mut textual_in_scope = false;
    let (last, mods) = match path_to_item.split_last() {
        Some(split) => split,
        None => return ItemMacroResolution::Other,
    };
    let Some(syn::Item::Macro(target)) = ({
        let mut cursor = items;
        let mut ok = true;
        for &index in mods {
            match cursor.get(index) {
                Some(syn::Item::Mod(module)) => match &module.content {
                    Some((_, inner)) => cursor = inner,
                    None => ok = false,
                },
                _ => ok = false,
            }
        }
        if ok {
            cursor.get(*last)
        } else {
            None
        }
    }) else {
        return ItemMacroResolution::Other;
    };
    let path = &target.mac.path;
    let Some(name_seg) = path.segments.last() else {
        return ItemMacroResolution::Other;
    };
    let name = name_seg.ident.to_string();
    if path.segments.len() == 2 {
        let index = MacroScopeIndex::from_file(file);
        let root = path.segments[0].ident.to_string();
        if root == "trust_vc"
            && !index.rebound_roots.contains("trust_vc")
            && path.segments.iter().all(|s| s.arguments.is_empty())
        {
            return ItemMacroResolution::TrustVc;
        }
        return ItemMacroResolution::Other;
    }
    if path.segments.len() != 1 || path.leading_colon.is_some() {
        return ItemMacroResolution::Other;
    }
    // Bare: textual macro_rules scope.
    for (depth, &index) in path_to_item.iter().enumerate() {
        let before = &items[..index];
        if before.iter().any(|item| is_macro_rules_named(item, &name)) {
            textual_in_scope = true;
        }
        if depth + 1 < path_to_item.len() {
            match &items[index] {
                syn::Item::Mod(module) => match &module.content {
                    Some((_, inner)) => items = inner,
                    None => return ItemMacroResolution::Other,
                },
                _ => return ItemMacroResolution::Other,
            }
        }
    }
    let exported = file_exports_macro(&file.items, &name, false);
    if (textual_in_scope || exported) && !item_list_binds_by_use(items, &name) {
        ItemMacroResolution::LocalMacroRules
    } else {
        ItemMacroResolution::Other
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn item_resolution(src: &str, path: &[usize]) -> ItemMacroResolution {
        let file: File = syn::parse_file(src).unwrap();
        resolve_item_macro(&file, path)
    }

    #[test]
    fn item_macro_resolution_covers_trust_vc_local_and_foreign() {
        use ItemMacroResolution::*;
        assert_eq!(
            item_resolution("trust_vc::state_machine!{ X {} }", &[0]),
            TrustVc
        );
        assert_eq!(
            item_resolution("::trust_vc::state_machine!{ X {} }", &[0]),
            TrustVc
        );
        assert_eq!(
            item_resolution("mod trust_vc {} trust_vc::state_machine!{ X {} }", &[1]),
            Other
        );
        assert_eq!(
            item_resolution("use x as trust_vc; trust_vc::state_machine!{ X {} }", &[1]),
            Other
        );
        assert_eq!(item_resolution("m::state_machine!{ X {} }", &[0]), Other);
        assert_eq!(item_resolution("state_machine!{ X {} }", &[0]), Other);
        assert_eq!(
            item_resolution(
                "macro_rules! state_machine { ($($t:tt)*) => {} } state_machine!{ X {} }",
                &[1]
            ),
            LocalMacroRules
        );
        // Declared AFTER the invocation: not textually in scope.
        assert_eq!(
            item_resolution(
                "state_machine!{ X {} } macro_rules! state_machine { ($($t:tt)*) => {} }",
                &[0]
            ),
            Other
        );
        assert_eq!(
            item_resolution(
                "use verus_state_machines_macros::state_machine; state_machine!{ X {} }",
                &[1]
            ),
            Other
        );
        assert_eq!(
            item_resolution(
                "mod m { macro_rules! state_machine { ($($t:tt)*) => {} } state_machine!{ X {} } }",
                &[0, 1]
            ),
            LocalMacroRules
        );
        // A module-local macro_rules does not reach the parent.
        assert_eq!(
            item_resolution(
                "mod m { macro_rules! state_machine { ($($t:tt)*) => {} } } state_machine!{ X {} }",
                &[1]
            ),
            Other
        );
        assert_eq!(
            item_resolution(
                "mod m { #[macro_export] macro_rules! state_machine { ($($t:tt)*) => {} } } state_machine!{ X {} }",
                &[1]
            ),
            LocalMacroRules
        );
    }

    /// The literal list `is_supported_body_macro_name` carried before it was
    /// derived from [`SPEC_MACRO_NAMES`]. Pins the derivation as
    /// behaviour-preserving.
    fn literal_body_lane_names(name: &str) -> bool {
        matches!(
            name,
            "assert"
                | "trust_vc_assert"
                | "assume"
                | "trust_vc_assume"
                | "reveal"
                | "trust_vc_reveal"
                | "hide"
                | "trust_vc_hide"
                | "invariant"
                | "trust_vc_invariant"
                | "invariant_except_break"
                | "trust_vc_invariant_except_break"
                | "loop_ensures"
                | "trust_vc_loop_ensures"
                | "loop_decreases"
                | "trust_vc_loop_decreases"
                | "broadcast_use"
                | "trust_vc_broadcast_use"
                | "assert_eq"
                | "assert_ne"
                | "assert_seqs_equal"
                | "calc"
                | "assert_forall_by"
                | "assert_by_nonlinear"
                | "assert_by_bit_vector"
                | "assert_by_compute"
                | "assert_by_contradiction"
                | "debug_assert"
                | "debug_assert_eq"
                | "debug_assert_ne"
        )
    }

    #[test]
    fn body_lane_name_set_is_unchanged_by_the_derivation() {
        for name in SPEC_MACRO_NAMES {
            assert_eq!(
                is_body_lane_supported_macro_name(name),
                literal_body_lane_names(name),
                "body-lane membership changed for `{name}`"
            );
        }
        for name in [
            "macro_rules",
            "println",
            "vec",
            QUARANTINED_MACRO_NAME,
            "seq",
            "old",
        ] {
            assert!(!is_body_lane_supported_macro_name(name));
            assert!(!literal_body_lane_names(name));
        }
    }

    #[test]
    fn quarantined_marker_is_not_a_recognised_name() {
        assert!(!SPEC_MACRO_NAMES.contains(&QUARANTINED_MACRO_NAME));
    }

    fn index_of(src: &str) -> MacroScopeIndex {
        MacroScopeIndex::from_file(&syn::parse_file(src).expect("probe file parses"))
    }

    fn resolves(src: &str, module: &[String], root: Option<&str>, name: &str) -> bool {
        let index = index_of(src);
        MacroPathScopes {
            use_site_module: Some(module),
            index: &index,
        }
        .resolves_to_well_known(root, name)
    }

    #[test]
    fn an_unshadowed_bare_name_resolves() {
        assert!(resolves("fn f() {}", &[], None, "assume"));
    }

    #[test]
    fn a_top_level_macro_rules_shadows_the_bare_name() {
        let src = "macro_rules! assume { ($e:expr) => {}; }";
        assert!(!resolves(src, &[], None, "assume"));
        // and only that name
        assert!(resolves(src, &[], None, "assert"));
    }

    #[test]
    fn a_macro_rules_in_a_module_does_not_shadow_the_parent() {
        let src = "mod m { macro_rules! assume { ($e:expr) => {}; } }";
        assert!(resolves(src, &[], None, "assume"));
        assert!(!resolves(src, &["m".to_string()], None, "assume"));
    }

    #[test]
    fn a_macro_export_escapes_its_module() {
        let src = "mod m { #[macro_export] macro_rules! assume { ($e:expr) => {}; } }";
        assert!(!resolves(src, &[], None, "assume"));
    }

    #[test]
    fn a_use_from_trust_vc_is_not_a_shadow() {
        assert!(resolves(
            "use trust_vc::{assume, invariant};",
            &[],
            None,
            "assume"
        ));
    }

    #[test]
    fn a_use_rename_onto_a_special_name_is_a_shadow() {
        assert!(!resolves("use util::noop as assume;", &[], None, "assume"));
        // even when the SOURCE is trust-vc: the name now means a different macro
        assert!(!resolves(
            "use trust_vc::hide as assume;",
            &[],
            None,
            "assume"
        ));
    }

    #[test]
    fn a_foreign_qualifier_never_resolves() {
        assert!(!resolves("fn f() {}", &[], Some("m"), "assume"));
        assert!(resolves("fn f() {}", &[], Some("trust_vc"), "assume"));
        assert!(resolves("fn f() {}", &[], Some("std"), "matches"));
    }

    #[test]
    fn the_ghost_collection_roots_the_corpus_writes_resolve() {
        assert!(resolves("fn f() {}", &[], Some("trust_vc_types"), "seq"));
        assert!(resolves("fn f() {}", &[], Some("vstd"), "seq"));
        assert!(resolves("fn f() {}", &[], Some("trust_vc"), "ext_eq"));
    }

    /// `crate::seq!` is not a foreign crate — it points back into this file, so
    /// it must get the SHADOW check, not an allowlist waiver. Believing `crate`
    /// as a root would have let a file's own `macro_rules! assume` be reached as
    /// `crate::assume!` and trusted.
    #[test]
    fn crate_and_self_are_resolved_against_this_file_not_allowlisted() {
        assert!(resolves("fn f() {}", &[], Some("crate"), "seq"));
        assert!(!resolves(
            "macro_rules! seq { ($($e:expr),*) => { 0 }; }",
            &[],
            Some("crate"),
            "seq"
        ));
        // `self::` is the USE SITE's module, not the crate root.
        let src = "mod m { macro_rules! seq { ($($e:expr),*) => { 0 }; } }";
        assert!(!resolves(src, &["m".to_string()], Some("self"), "seq"));
        assert!(resolves(src, &[], Some("self"), "seq"));
        // `super::` cannot be resolved from one file and is declined.
        assert!(!resolves(
            "fn f() {}",
            &["m".to_string()],
            Some("super"),
            "seq"
        ));
    }

    #[test]
    fn a_rebound_root_stops_being_believed() {
        assert!(!resolves(
            "mod trust_vc { }",
            &[],
            Some("trust_vc"),
            "assume"
        ));
        assert!(!resolves(
            "use other::thing as trust_vc;",
            &[],
            Some("trust_vc"),
            "assume"
        ));
        assert!(!resolves(
            "extern crate other as core;",
            &[],
            Some("core"),
            "matches"
        ));
    }

    #[test]
    fn an_unknown_use_site_module_falls_back_to_any_shadow() {
        let index = index_of("mod m { macro_rules! assume { ($e:expr) => {}; } }");
        let scopes = MacroPathScopes {
            use_site_module: None,
            index: &index,
        };
        assert!(!scopes.resolves_to_well_known(None, "assume"));
        assert!(scopes.resolves_to_well_known(None, "assert"));
    }

    #[test]
    fn path_root_reads_the_first_segment_not_the_last() {
        let tokens: Vec<TokenTree> = "a :: b ::"
            .parse::<TokenStream>()
            .unwrap()
            .into_iter()
            .collect();
        assert_eq!(path_root_before(&tokens).as_deref(), Some("a"));
        assert_eq!(path_root_before(&[]), None);
    }

    #[test]
    fn a_not_equals_is_not_a_macro_invocation() {
        let trees: Vec<TokenTree> = "assume != (x)"
            .parse::<TokenStream>()
            .unwrap()
            .into_iter()
            .collect();
        assert!(!begins_macro_invocation(&trees, 0));
        let trees: Vec<TokenTree> = "assume!(x)"
            .parse::<TokenStream>()
            .unwrap()
            .into_iter()
            .collect();
        assert!(begins_macro_invocation(&trees, 0));
    }

    #[test]
    fn an_unshadowed_function_is_handed_back_untouched() {
        let file: File = syn::parse_file("fn f() { trust_vc::assume!(x); assume!(y); }").unwrap();
        let syn::Item::Fn(func) = &file.items[0] else {
            panic!("expected a fn")
        };
        assert!(quarantine_shadowed_spec_macros(func, Some(&file), Some(&[])).is_none());
    }

    #[test]
    fn a_shadowed_invocation_is_rewritten_everywhere_it_is_written() {
        let file: File = syn::parse_file(
            "macro_rules! assume { ($e:expr) => {}; }
             fn f() {
                 assume!(x);
                 trust_vc::proof_block!({ assume!(y); });
                 trust_vc::assume!(z);
             }",
        )
        .unwrap();
        let syn::Item::Fn(func) = &file.items[1] else {
            panic!("expected a fn")
        };
        let rewritten = quarantine_shadowed_spec_macros(func, Some(&file), Some(&[]))
            .expect("the shadowed invocations are quarantined");
        let rendered = rewritten.to_token_stream().to_string();
        assert_eq!(
            rendered.matches(QUARANTINED_MACRO_NAME).count(),
            2,
            "both the statement-position and the token-stream-nested invocation: {rendered}"
        );
        assert!(
            rendered.contains("trust_vc :: assume"),
            "the explicitly qualified one is left alone: {rendered}"
        );
    }
}
