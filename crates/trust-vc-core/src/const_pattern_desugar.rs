//! Source-level desugaring of `const`-NAME patterns into their literal value.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # The hole this closes
//!
//! A bare identifier in pattern position is NOT always a binding. Rust resolves
//! it against the value namespace's ITEMS first: when a `const` of that name is
//! in scope the pattern is REFUTABLE and matches only scrutinees equal to the
//! const's value (`E0530` even forbids a binding from shadowing a constant).
//!
//! Every pattern predicate in the extractor decided this by SPELLING — an
//! uppercase-initial ident was treated as a const/variant, a lowercase one as a
//! binder. That heuristic is wrong in both directions, and one of them was a
//! CARDINAL FALSE VERIFY:
//!
//! ```ignore
//! const K: u64 = 5;
//! #[trust_vc::requires(n < 100)]
//! pub fn f(n: u64) { match n { K => {} _ => { assert!(false); } } }   // VERIFIED
//! ```
//!
//! `arm_pattern_match_condition` classified the `K` arm as `Always` (it is not a
//! datatype variant, so it fell through to the bare-binder answer), which made
//! the wildcard arm's prior-negation `!(true)` — FALSE — and vacuously
//! discharged `assert!(false)`. Replacing `K` with its own value `5` refutes,
//! which is the discriminator that proves the defect.
//!
//! # The rewrite
//!
//! Decide by DECLARATION, not by spelling. Collect the file's declared
//! `const`/`static` names, then in pattern positions where Rust would perform
//! that item resolution (match arms, `let`-`else`, `if let` / `while let`):
//!
//! * a name declared as a file-top-level `const` with a LITERAL initializer is
//!   replaced by that literal — a `Pat::Lit`, the shape every lane already
//!   models soundly (`arm_pattern_match_condition` renders `scrutinee == lit`);
//! * any other declared const/static name is renamed to the reserved
//!   [`UNMODELED_CONST_PAT_PREFIX`] marker, which every pattern lane fails
//!   closed on.
//!
//! # Soundness
//!
//! The literal substitution is Rust's own semantics for the pattern, so it is
//! behavior-preserving; it can only turn a previously fail-closed (or falsely
//! verified) function into a soundly verified or refuted one.
//!
//! Two ways a substitution could be WRONG are excluded by construction:
//!
//! * **Wrong value.** A name declared more than once anywhere in the file (a
//!   nested `mod` shadow, a second declaration) is never folded — it goes to
//!   the fail-closed marker instead. Only a UNIQUE, file-top-level declaration
//!   is trusted to be the one a bare pattern name resolves to.
//! * **Not actually a const pattern.** Associated consts (`impl S { const K }`,
//!   trait items) are deliberately NOT collected: a bare `K` does not resolve
//!   to them (`S::K` is required), so treating one as a const pattern would
//!   convert a genuine BINDER into a literal — which narrows the arm's path
//!   condition and is the false-verify direction. Signature patterns are never
//!   rewritten for the same reason.
//!
//! Over-collection (a nested-`mod` or fn-local const name colliding with an
//! ordinary binder elsewhere) only ever routes to the marker, i.e. fail closed.
//!
//! # `use` aliases
//!
//! A registry keyed on DECLARATION idents alone is defeated by a `use`, which
//! introduces a second NAME for the same const:
//!
//! ```ignore
//! #![allow(non_upper_case_globals)]
//! pub const lower_k: u64 = 5;
//! use crate::lower_k as alias_k;
//!
//! #[trust_vc::requires(n < 100)]
//! pub fn f(n: u64) { match n { alias_k => {} _ => { assert!(false); } } }  // VERIFIED
//! ```
//!
//! Same const, same file, two names, two verdicts — the aliased one was the
//! identical cardinal false verify the declaration route already closed. So the
//! file's top-level `use` items are resolved back to the item they NAME and the
//! local name is entered in the same registry: the declaration decides, not the
//! spelling. An `as` rename of an UPPERCASE const to a lowercase local defeats
//! the spelling heuristic too, so this is not a case residual.
//!
//! The narrowness pin runs the other way: an import that resolves to something
//! a bare pattern ident CANNOT name — a function, a type, a trait, a module, a
//! struct with fields — is NOT entered, because `use std::cmp::min;` must leave
//! `match n { min => .. }` binding. Only const-like imports may change
//! behaviour.
//!
//! A `use` this file cannot resolve (an external crate, `super::`, an
//! out-of-line `mod m;`, an edition-2018 bare-crate prefix) enters as
//! [`ConstPatternValue::Unmodeled`] — fail closed on that ONE name, never on
//! unrelated binders.
//!
//! A `use` below file scope is collected too — a function inside one is
//! verified, so its aliases cannot be invisible — but its value is never
//! FOLDED, only failed closed. That mirrors the treatment of a nested const
//! DECLARATION exactly, and for the same reason: this pass does not model
//! scope, so a value it took from the wrong scope could narrow an arm's path
//! condition, which is the false-verify direction.
//!
//! # SCOPE — the axis that spelling coverage does not reach
//!
//! Deciding by declaration only helps if the declaration is SEEN. The first
//! version of this collector descended into `Item::Mod` content and the
//! top-level `Stmt::Item` list of an `Item::Fn` block, and nowhere else. A
//! `const` — or a `use` alias — declared in an `impl` method body, a trait
//! DEFAULT method body, or ANY nested block was therefore never registered,
//! stayed a bare lowercase ident, and reproduced the original cardinal false
//! verify in full:
//!
//! ```ignore
//! impl S {
//!     #[trust_vc::requires(n < 100)]
//!     pub fn f(n: u64) -> u64 {
//!         const lower_k: u64 = 5;
//!         match n { lower_k => 1, _ => { assert!(false); 0 } }   // VERIFIED
//!     }
//! }
//! ```
//!
//! Four container shapes, four false verifies (impl method body, trait default
//! body, nested block, nested block inside an impl method). Adding three match
//! arms would have closed those four and left the fifth shape open, so
//! [`ScopeScan`] walks the WHOLE file with `syn::visit::Visit` instead: every
//! scope that can hold a `const`, a `static` or a `use` is covered by
//! construction, and associated consts stay excluded because they are different
//! syn nodes rather than because a match arm omits them.
//!
//! Residual, deliberately not blanket-rejected: an unresolvable GLOB
//! (`use other_crate::prelude::*;`) names nothing, so a const it brings in is
//! invisible here. Failing closed on every bare binder in a glob-importing file
//! would reject essentially the whole corpus (`use vstd::prelude::*;`), so the
//! glob is skipped. The exposure is only a LOWERCASE const behind an
//! unresolvable glob — an uppercase one still fails closed downstream in
//! `arm_pattern_match_condition`. A glob over an INLINE module is already
//! covered: `all_names` collects consts declared anywhere in the file.
//!
//! # MACRO GRAMMAR — the second axis, and the same lesson twice
//!
//! Seeing the declaration only helps if the PATTERN is reached, and syn visitors
//! do not descend into macro or attribute token streams.
//! [`ConstPatternRewriter::rewrite_tokens`] is the only bridge across that gap,
//! and its first version re-parsed the stream as one `syn::Expr`, answering
//! `None` otherwise — the same value it answers when nothing needs rewriting.
//! Every supported body macro whose grammar is not a single expression was
//! therefore skipped in silence, and the original cardinal false verify came
//! back verbatim inside each one. Measured at the CLI, five of them:
//! `assert_eq!`, `assert_ne!`, `assert_by!`, `assert_by_contradiction!`,
//! `calc!`. The plain `assert!` — the one shape that already parsed as an
//! `Expr` — refuted correctly throughout, which is the discriminator.
//!
//! The scope axis was fixed by walking the whole tree instead of enumerating
//! container shapes; this one is fixed the same way. [`TokenRewrite`] gives
//! "nothing to rewrite" and "cannot tell" different values, and the reach is a
//! parse CASCADE (expression · expression list · statement list · Verus spec
//! surface · structural salvage) in which no step is keyed on a macro NAME, so
//! the tenth macro needs no tenth arm.

use quote::{quote, ToTokens};
use std::collections::{BTreeMap, BTreeSet};
use syn::visit_mut::VisitMut;
use syn::{Attribute, Expr, ExprLet, File, Item, Lit, Local, Meta, Pat, Stmt, UseTree};

/// Reserved rename applied to a pattern naming a declared `const`/`static`
/// whose value this pass cannot fold. The prefix is uppercase-initial, so the
/// existing const-pattern rejections in `ir_lowering::match_lowering::
/// lower_pattern`, `pattern_is_irrefutable_binder` and
/// `pattern_match_condition_for_scoped_value` already fail closed on it;
/// `arm_pattern_match_condition` recognises the prefix explicitly.
pub(crate) const UNMODELED_CONST_PAT_PREFIX: &str = "TrustVcUnmodeledConstPat_";

/// The original const name behind an [`UNMODELED_CONST_PAT_PREFIX`] marker, for
/// diagnostics.
pub(crate) fn unmodeled_const_pat_name(ident: &str) -> Option<&str> {
    ident.strip_prefix(UNMODELED_CONST_PAT_PREFIX)
}

/// What a declared name resolves to in pattern position.
#[derive(Clone)]
enum ConstPatternValue {
    /// A unique file-top-level `const` with a literal initializer.
    Literal(Lit),
    /// Declared, but this pass will not vouch for the value (non-literal
    /// initializer, nested/fn-local declaration, `static`, or a duplicated
    /// name). Fails closed.
    Unmodeled,
}

/// Literal initializers this pass folds. Deliberately narrow:
///
/// * floats are excluded — pattern equality on a float is not the SMT equality
///   the literal arm renders;
/// * strings/byte-strings are excluded — no scalar equality to render;
/// * a NEGATED literal (`-5`) is excluded — it is an `Expr::Unary`, not an
///   `Expr::Lit`, and syn's `Pat::Lit` cannot carry the sign.
fn foldable_literal(expr: &Expr) -> Option<Lit> {
    let Expr::Lit(expr_lit) = expr else {
        return None;
    };
    match &expr_lit.lit {
        lit @ (Lit::Int(_) | Lit::Bool(_) | Lit::Char(_) | Lit::Byte(_)) => Some(lit.clone()),
        _ => None,
    }
}

/// Every `const`/`static` declaration and every `use` alias in the file,
/// gathered from EVERY syntactic scope that can hold one.
///
/// Deliberately a whole-tree [`syn::visit::Visit`] rather than a hand-rolled
/// item walk. The hand-rolled predecessor descended only into `Item::Mod`
/// content and the TOP-LEVEL statement items of an `Item::Fn` block, so a
/// `const` (or a `use`) declared in an `impl` method body, a trait DEFAULT
/// method body, or ANY nested block was invisible. The name then stayed a bare
/// lowercase ident, `arm_pattern_match_condition` answered `Always`, and the
/// sibling arm's prior-negation `!(true)` — FALSE — vacuously discharged it:
/// four cardinal false verifies, one per container shape. Enumerating container
/// shapes is how that hole got dug in the first place, so this walks the whole
/// tree instead and the next shape needs no fourth patch.
///
/// ASSOCIATED consts stay excluded for free, and that is not an accident of
/// this encoding: `ImplItem::Const` and `TraitItem::Const` are distinct syn
/// nodes that never reach [`syn::visit::Visit::visit_item_const`]. A bare `K`
/// cannot name one (`S::K` is required), so collecting one would convert a
/// genuine BINDER into a fail-closed marker for no soundness gain.
#[derive(Default)]
struct ScopeScan {
    /// Declaration counts. A name seen more than once anywhere is never folded.
    all_names: BTreeMap<String, usize>,
    /// `(local_name, full_path_segments)` for every `use` below file scope.
    uses: Vec<(String, Vec<String>)>,
}

impl<'ast> syn::visit::Visit<'ast> for ScopeScan {
    fn visit_item_const(&mut self, node: &'ast syn::ItemConst) {
        *self.all_names.entry(node.ident.to_string()).or_insert(0) += 1;
        // Keep descending: a `const X: u64 = { const inner: u64 = 3; inner };`
        // still declares `inner` in a scope this pass cannot place.
        syn::visit::visit_item_const(self, node);
    }

    fn visit_item_static(&mut self, node: &'ast syn::ItemStatic) {
        *self.all_names.entry(node.ident.to_string()).or_insert(0) += 1;
        syn::visit::visit_item_static(self, node);
    }

    fn visit_item_use(&mut self, node: &'ast syn::ItemUse) {
        flatten_use_tree(&node.tree, &mut Vec::new(), &mut self.uses);
    }
}

/// Collect every declared name a bare pattern identifier could resolve to.
///
/// `top_level` records file-scope `const` items (the only ones whose value is
/// folded); the scan's `all_names` records EVERY const/static declaration found
/// anywhere the bare name could be in scope, so a duplicate demotes the folded
/// entry to `Unmodeled`.
///
/// Associated consts are excluded: see the module soundness note.
fn collect_declared_consts(file: &File) -> BTreeMap<String, ConstPatternValue> {
    let mut top_level: BTreeMap<String, Lit> = BTreeMap::new();
    let mut top_uses: Vec<(String, Vec<String>)> = Vec::new();
    let mut scan = ScopeScan::default();

    for item in &file.items {
        match item {
            Item::Const(item_const) => {
                if let Some(lit) = foldable_literal(&item_const.expr) {
                    top_level.insert(item_const.ident.to_string(), lit);
                }
            }
            // A file-top-level `use` carries the fold permission, so it is
            // gathered here and NOT handed to the scanner: entering the same
            // alias twice would make `enter_alias` demote it to `Unmodeled` and
            // silently retire the alias-fold capability.
            Item::Use(item_use) => {
                flatten_use_tree(&item_use.tree, &mut Vec::new(), &mut top_uses);
                continue;
            }
            _ => {}
        }
        syn::visit::Visit::visit_item(&mut scan, item);
    }

    let mut declared: BTreeMap<String, ConstPatternValue> = scan
        .all_names
        .into_iter()
        .map(|(name, count)| {
            let value = match top_level.get(&name) {
                Some(lit) if count == 1 => ConstPatternValue::Literal(lit.clone()),
                _ => ConstPatternValue::Unmodeled,
            };
            (name, value)
        })
        .collect();

    merge_use_aliases(file, top_uses, scan.uses, &mut declared);
    declared
}

/// What a `use` binds its local name to, for pattern purposes.
enum UseTarget {
    /// Resolved to an in-file item a bare pattern ident CANNOT name (a `fn`, a
    /// type, a trait, a module, a struct with fields). The local name still
    /// BINDS — this is the narrowness pin, and such an import is never entered
    /// in the registry.
    Binder,
    /// Resolved to a unique in-file `const` with a foldable literal initializer.
    Literal(Lit),
    /// Const-like but not vouched for (non-literal initializer, `static`, unit
    /// struct/variant), or not resolvable in this file at all. Fails closed.
    Unmodeled,
}

/// Enter every `use` alias in the registry under its LOCAL name.
///
/// A name already present from a declaration is demoted to `Unmodeled` rather
/// than overwritten: the two spellings disagreeing means this pass has lost
/// track of which item the pattern resolves to, and guessing either way is the
/// unsound direction.
fn merge_use_aliases(
    file: &File,
    top_uses: Vec<(String, Vec<String>)>,
    nested_uses: Vec<(String, Vec<String>)>,
    declared: &mut BTreeMap<String, ConstPatternValue>,
) {
    let imports = top_uses
        .into_iter()
        .map(|(local, path)| (local, path, true))
        .chain(
            nested_uses
                .into_iter()
                .map(|(local, path)| (local, path, false)),
        );

    for (local, path, top) in imports {
        // A `use` nested in an inline `mod` or a fn body is in scope only there,
        // and a `self::`-rooted path inside one does not even mean what it means
        // at file root — so it is resolved for CLASSIFICATION only and never
        // folded. Exactly how a nested/fn-local const DECLARATION is treated.
        if !top && path.first().is_some_and(|root| root != "crate") {
            // Unresolvable from here: fail closed on this one name.
            enter_alias(declared, local, ConstPatternValue::Unmodeled);
            continue;
        }
        let target = resolve_import(file, &path);
        let value = match target {
            // The pin: a fn/type/mod import leaves an ordinary binder alone.
            UseTarget::Binder => continue,
            UseTarget::Literal(lit) if top => ConstPatternValue::Literal(lit),
            UseTarget::Literal(_) | UseTarget::Unmodeled => ConstPatternValue::Unmodeled,
        };
        enter_alias(declared, local, value);
    }
}

/// Enter one alias, demoting a name that is already spoken for.
fn enter_alias(
    declared: &mut BTreeMap<String, ConstPatternValue>,
    local: String,
    value: ConstPatternValue,
) {
    match declared.entry(local) {
        std::collections::btree_map::Entry::Vacant(slot) => {
            slot.insert(value);
        }
        std::collections::btree_map::Entry::Occupied(mut slot) => {
            slot.insert(ConstPatternValue::Unmodeled);
        }
    }
}

/// Flatten a `use` tree into `(local_name, full_path_segments)` pairs.
///
/// A glob contributes nothing: it names no local, so there is nothing to enter
/// (see the module note on the glob residual).
fn flatten_use_tree(
    tree: &UseTree,
    prefix: &mut Vec<String>,
    out: &mut Vec<(String, Vec<String>)>,
) {
    match tree {
        UseTree::Path(path) => {
            prefix.push(path.ident.to_string());
            flatten_use_tree(&path.tree, prefix, out);
            prefix.pop();
        }
        UseTree::Name(name) => {
            let ident = name.ident.to_string();
            // `use m::{self, X}` re-exports the module, binding no new value name.
            if matches!(ident.as_str(), "self" | "crate" | "super") {
                return;
            }
            let mut full = prefix.clone();
            full.push(ident.clone());
            out.push((ident, full));
        }
        UseTree::Rename(rename) => {
            let mut full = prefix.clone();
            full.push(rename.ident.to_string());
            out.push((rename.rename.to_string(), full));
        }
        UseTree::Group(group) => {
            for item in &group.items {
                flatten_use_tree(item, prefix, out);
            }
        }
        UseTree::Glob(_) => {}
    }
}

/// Resolve an imported path against this file's own item tree.
///
/// Only a `crate::`- or `self::`-rooted path can be resolved: in edition 2018 a
/// bare leading segment names an external crate, and `super::` leaves the file.
/// Anything unresolved is [`UseTarget::Unmodeled`] — fail closed on that one
/// name rather than guess what it denotes.
fn resolve_import(file: &File, path: &[String]) -> UseTarget {
    let Some((root, rest)) = path.split_first() else {
        return UseTarget::Unmodeled;
    };
    if root != "crate" && root != "self" {
        return UseTarget::Unmodeled;
    }
    let Some((last, mods)) = rest.split_last() else {
        return UseTarget::Unmodeled;
    };

    let mut items: &[Item] = &file.items;
    for segment in mods {
        let mut next: Option<&[Item]> = None;
        for item in items {
            match item {
                Item::Mod(item_mod) if item_mod.ident == segment.as_str() => {
                    // An out-of-line `mod m;` has no content here.
                    let Some((_, inner)) = &item_mod.content else {
                        return UseTarget::Unmodeled;
                    };
                    next = Some(inner);
                }
                // `use crate::E::V;` — a variant, not a module. Unit variants are
                // refutable patterns, so fail closed rather than resolve further.
                Item::Enum(item_enum) if item_enum.ident == segment.as_str() => {
                    return UseTarget::Unmodeled;
                }
                _ => {}
            }
        }
        match next {
            Some(inner) => items = inner,
            None => return UseTarget::Unmodeled,
        }
    }

    // A name can match in two namespaces at once (`struct Foo; fn Foo() {}`), so
    // collect every candidate and take the most conservative answer.
    let mut candidates: Vec<UseTarget> = Vec::new();
    for item in items {
        let hit = match item {
            Item::Const(item_const) if item_const.ident == last.as_str() => {
                match foldable_literal(&item_const.expr) {
                    Some(lit) => UseTarget::Literal(lit),
                    None => UseTarget::Unmodeled,
                }
            }
            Item::Static(item_static) if item_static.ident == last.as_str() => UseTarget::Unmodeled,
            // A unit struct IS a refutable pattern; one with fields is not a
            // value-namespace pattern at all.
            Item::Struct(item_struct) if item_struct.ident == last.as_str() => {
                match item_struct.fields {
                    syn::Fields::Unit => UseTarget::Unmodeled,
                    _ => UseTarget::Binder,
                }
            }
            Item::Fn(item_fn) if item_fn.sig.ident == last.as_str() => UseTarget::Binder,
            Item::Mod(item_mod) if item_mod.ident == last.as_str() => UseTarget::Binder,
            Item::Enum(item_enum) if item_enum.ident == last.as_str() => UseTarget::Binder,
            Item::Trait(item_trait) if item_trait.ident == last.as_str() => UseTarget::Binder,
            Item::Type(item_type) if item_type.ident == last.as_str() => UseTarget::Binder,
            Item::Union(item_union) if item_union.ident == last.as_str() => UseTarget::Binder,
            _ => continue,
        };
        candidates.push(hit);
    }

    match candidates.len() {
        0 => UseTarget::Unmodeled,
        1 => candidates.pop().expect("one candidate"),
        _ if candidates.iter().all(|c| matches!(c, UseTarget::Binder)) => UseTarget::Binder,
        _ => UseTarget::Unmodeled,
    }
}

struct ConstPatternRewriter<'a> {
    consts: &'a BTreeMap<String, ConstPatternValue>,
    rewrote: bool,
}

impl ConstPatternRewriter<'_> {
    /// Rewrite the const names inside a pattern, recursing through every
    /// composite shape. Called ONLY from refutable pattern positions.
    fn rewrite_pat(&mut self, pat: &mut Pat) {
        match pat {
            Pat::Ident(ident) => {
                // `ref x` / `mut x` / `x @ SUB` are unambiguously BINDINGS — Rust
                // never resolves them to a const — so they keep their meaning.
                if ident.by_ref.is_some() || ident.mutability.is_some() {
                    return;
                }
                if let Some((_, subpat)) = &mut ident.subpat {
                    self.rewrite_pat(subpat);
                    return;
                }
                let name = ident.ident.to_string();
                match self.consts.get(&name) {
                    Some(ConstPatternValue::Literal(lit)) => {
                        *pat = Pat::Lit(syn::PatLit {
                            attrs: Vec::new(),
                            lit: lit.clone(),
                        });
                        self.rewrote = true;
                    }
                    Some(ConstPatternValue::Unmodeled) => {
                        ident.ident = syn::Ident::new(
                            &format!("{UNMODELED_CONST_PAT_PREFIX}{name}"),
                            ident.ident.span(),
                        );
                        self.rewrote = true;
                    }
                    None => {}
                }
            }
            Pat::Or(or_pat) => {
                for case in &mut or_pat.cases {
                    self.rewrite_pat(case);
                }
            }
            Pat::Paren(paren) => self.rewrite_pat(&mut paren.pat),
            Pat::Reference(reference) => self.rewrite_pat(&mut reference.pat),
            Pat::Type(pat_type) => self.rewrite_pat(&mut pat_type.pat),
            Pat::Tuple(tuple) => {
                for elem in &mut tuple.elems {
                    self.rewrite_pat(elem);
                }
            }
            Pat::TupleStruct(tuple_struct) => {
                for elem in &mut tuple_struct.elems {
                    self.rewrite_pat(elem);
                }
            }
            Pat::Slice(slice) => {
                for elem in &mut slice.elems {
                    self.rewrite_pat(elem);
                }
            }
            Pat::Struct(strukt) => {
                for field in &mut strukt.fields {
                    let was_shorthand = field.colon_token.is_none();
                    self.rewrite_pat(&mut field.pat);
                    // `S { kk }` shorthand cannot carry a non-ident pattern; once
                    // rewritten it must be spelled `S { kk: 5 }` or the AST
                    // re-tokenizes into invalid source.
                    if was_shorthand && !matches!(&*field.pat, Pat::Ident(_)) {
                        field.colon_token = Some(syn::token::Colon::default());
                    }
                }
            }
            _ => {}
        }
    }

    /// A fresh rewriter over the same registry, for rewriting a sub-stream
    /// without disturbing this one's `rewrote` flag.
    fn child(&self) -> ConstPatternRewriter<'_> {
        ConstPatternRewriter {
            consts: self.consts,
            rewrote: false,
        }
    }

    /// Rewrite inside a macro or attribute token stream.
    ///
    /// syn visitors do not descend into macro/attribute streams, so this is the
    /// ONLY path by which the desugar reaches a pattern inside one.
    ///
    /// # The hole this closes
    ///
    /// The predecessor was one line — `syn::parse2::<Expr>(tokens).ok()?` — so
    /// it silently answered `None` for every stream that is not exactly ONE
    /// expression. `None` also meant "nothing here needed rewriting", so the two
    /// were indistinguishable and the caller read the second meaning. Every
    /// supported body macro with a non-`Expr` grammar therefore skipped the
    /// desugar entirely: `assert_eq!`, `assert_ne!`, `assert_seqs_equal!`,
    /// `assert_by!`, `assert_by_contradiction!`, `calc!`, `assert_forall_by!`,
    /// the `assert_by_*` solver-mode family. A const name in a match arm inside
    /// one was then neither FOLDED nor MARKED, `arm_pattern_match_condition`
    /// answered `Always`, the sibling arm's prior-negation `!(true)` was FALSE,
    /// and the discharge was VACUOUS — a CARDINAL false verify:
    ///
    /// ```ignore
    /// #![allow(non_upper_case_globals)]
    /// pub const kk: u64 = 5;
    /// #[trust_vc::requires(n == 7)]
    /// pub fn f(n: u64) { assert_eq!(match n { kk => 1u64, _ => 2u64 }, 1u64); }  // VERIFIED
    /// ```
    ///
    /// Spelling the same arm `5u64 =>` refutes, which is the discriminator.
    ///
    /// # The three answers
    ///
    /// [`TokenRewrite`] separates the two meanings that used to share `None`,
    /// and the third answer fails closed. The cascade is ordered
    /// most-precise-first and NONE of its steps is keyed on a macro NAME —
    /// enumerating macro shapes is how this hole got dug, so a tenth macro needs
    /// no tenth arm here.
    fn rewrite_tokens(&self, tokens: &proc_macro2::TokenStream) -> TokenRewrite {
        // EXACT gate, not a heuristic: a stream in which no registered name
        // occurs as an identifier at any depth cannot contain anything this pass
        // would rewrite. `Unchanged` here is a fact, and it is the only route by
        // which an unparseable stream is allowed to pass through untouched.
        if !self.mentions_registered_name(tokens) {
            return TokenRewrite::Unchanged;
        }
        self.rewrite_stream(tokens)
    }

    /// The parse cascade for a stream KNOWN to mention a registered name.
    fn rewrite_stream(&self, tokens: &proc_macro2::TokenStream) -> TokenRewrite {
        // R1 — one expression. `assert!`, `assume!`, `invariant!`,
        // `loop_decreases!`, a contract-attribute predicate.
        if let Some(answer) = self.rewrite_as_expr(tokens) {
            return answer;
        }
        // R2 — comma-separated expressions. `assert_eq!`, `assert_ne!`,
        // `assert_seqs_equal!(a, b)`, `assert_by!(c, { .. })`,
        // `assert_by_contradiction!(c, { .. })`, `assert!(c, "msg")`.
        if let Some(answer) = self.rewrite_as_expr_list(tokens) {
            return answer;
        }
        // R3 — a statement sequence. A brace-delimited proof body handed over
        // without its braces, and `calc!`'s `{ proof } expr` steps.
        if let Some(answer) = self.rewrite_as_stmts(tokens) {
            return answer;
        }
        // R4 — the Verus spec surface (`==>`, `<==>`, `forall|..|`, `=~=`, …),
        // which `syn` cannot parse. RECOGNIZER ONLY: the chain normalizer
        // rewrites those operators into marker macros, so re-emitting its output
        // would silently change the spec surface the extractor later re-parses.
        // It is therefore trusted only for the negative answer — "this stream is
        // a spec expression and it holds no foldable pattern" — which is exactly
        // what keeps `assert_by_bit_vector!(kk == 5 ==> b)` untouched.
        if let Some(answer) = self.recognize_spec_expr(tokens) {
            return answer;
        }
        // R5 — structural salvage.
        self.salvage_stream(tokens)
    }

    fn rewrite_as_expr(&self, tokens: &proc_macro2::TokenStream) -> Option<TokenRewrite> {
        let mut expr: Expr = syn::parse2(tokens.clone()).ok()?;
        let mut inner = self.child();
        inner.visit_expr_mut(&mut expr);
        Some(if inner.rewrote {
            TokenRewrite::Rewritten(quote!(#expr))
        } else {
            TokenRewrite::Unchanged
        })
    }

    fn rewrite_as_expr_list(&self, tokens: &proc_macro2::TokenStream) -> Option<TokenRewrite> {
        let parser = syn::punctuated::Punctuated::<Expr, syn::Token![,]>::parse_terminated;
        let mut args = syn::parse::Parser::parse2(parser, tokens.clone()).ok()?;
        if args.is_empty() {
            return None;
        }
        let mut inner = self.child();
        for arg in args.iter_mut() {
            inner.visit_expr_mut(arg);
        }
        Some(if inner.rewrote {
            TokenRewrite::Rewritten(quote!(#args))
        } else {
            TokenRewrite::Unchanged
        })
    }

    fn rewrite_as_stmts(&self, tokens: &proc_macro2::TokenStream) -> Option<TokenRewrite> {
        let mut stmts =
            syn::parse::Parser::parse2(syn::Block::parse_within, tokens.clone()).ok()?;
        if stmts.is_empty() {
            return None;
        }
        let mut inner = self.child();
        for stmt in &mut stmts {
            inner.visit_stmt_mut(stmt);
        }
        Some(if inner.rewrote {
            TokenRewrite::Rewritten(quote!(#(#stmts)*))
        } else {
            TokenRewrite::Unchanged
        })
    }

    /// `Some(Unchanged)` iff the stream is a Verus-surface spec expression that
    /// provably holds no pattern this pass would rewrite. Never returns tokens:
    /// see the R4 note.
    fn recognize_spec_expr(&self, tokens: &proc_macro2::TokenStream) -> Option<TokenRewrite> {
        let mut expr =
            crate::chained_comparisons::parse_expr_tokens_with_chains(tokens.clone()).ok()?;
        let mut inner = self.child();
        inner.visit_expr_mut(&mut expr);
        (!inner.rewrote).then_some(TokenRewrite::Unchanged)
    }

    /// R5. Split the stream at its TOP-LEVEL `,` / `;` separators and re-run the
    /// cascade on each piece; a piece that still does not parse is descended
    /// into structurally, and whatever is left is substituted name-by-name.
    fn salvage_stream(&self, tokens: &proc_macro2::TokenStream) -> TokenRewrite {
        let segments = split_top_level(tokens);
        if segments.len() > 1 {
            let mut out = proc_macro2::TokenStream::new();
            let mut folded = false;
            let mut marked = false;
            for segment in segments {
                match segment {
                    Segment::Separator(tree) => out.extend(std::iter::once(tree)),
                    Segment::Tokens(stream) => match self.rewrite_tokens(&stream) {
                        TokenRewrite::Unchanged => out.extend(stream),
                        TokenRewrite::Rewritten(new) => {
                            folded = true;
                            out.extend(new);
                        }
                        TokenRewrite::Unresolved(new) => {
                            marked = true;
                            out.extend(new);
                        }
                    },
                }
            }
            return TokenRewrite::from_flags(out, folded, marked);
        }
        self.descend_stream(tokens)
    }

    /// The floor of the cascade: this stream has no top-level separator to split
    /// on and matched no grammar, so its shape is unknown.
    ///
    /// Nested groups are still re-run through the whole cascade — that is what
    /// reaches the arms of a `match` sitting inside a `calc!` step, whose brace
    /// group parses as a comma-separated arm list nowhere but does split into
    /// per-arm segments here.
    ///
    /// Everything the cascade could not account for is then SUBSTITUTED rather
    /// than skipped, and that is sound in both readings of the tokens:
    ///
    /// * a `Literal` entry is a UNIQUE FILE-TOP-LEVEL const that is genuinely in
    ///   scope for this function (`desugar_const_patterns` demotes the whole
    ///   registry otherwise), so no legal binder can share its name — E0530
    ///   forbids a binding shadowing a constant. Folding it is Rust's own
    ///   semantics in pattern position AND value-preserving in expression
    ///   position, so this is not a rejection at all;
    /// * an `Unmodeled` entry becomes the reserved marker, which every pattern
    ///   lane already fails closed on — the standing treatment of that name
    ///   everywhere else in this pass, not a new hammer.
    ///
    /// A group whose content the cascade DID parse and found nothing in is still
    /// substituted, because "found nothing" was decided under an expression
    /// reading that an unparseable parent may contradict: `Some(kk)` inside a
    /// match arm list parses as a call expression, and reading it that way is
    /// precisely how the arm's const would keep its `Always` classification.
    fn descend_stream(&self, tokens: &proc_macro2::TokenStream) -> TokenRewrite {
        let trees: Vec<proc_macro2::TokenTree> = tokens.clone().into_iter().collect();
        let mut out = proc_macro2::TokenStream::new();
        let mut folded = false;
        let mut marked = false;

        for (index, tree) in trees.iter().enumerate() {
            match tree {
                proc_macro2::TokenTree::Group(group) => {
                    let inner = group.stream();
                    let replacement = match self.rewrite_tokens(&inner) {
                        TokenRewrite::Unchanged if self.mentions_registered_name(&inner) => {
                            let (substituted, did_fold, did_mark) = self.substitute_stream(&inner);
                            folded |= did_fold;
                            marked |= did_mark;
                            Some(substituted)
                        }
                        TokenRewrite::Unchanged => None,
                        TokenRewrite::Rewritten(new) => {
                            folded = true;
                            Some(new)
                        }
                        TokenRewrite::Unresolved(new) => {
                            marked = true;
                            Some(new)
                        }
                    };
                    match replacement {
                        Some(new) => {
                            let mut rebuilt = proc_macro2::Group::new(group.delimiter(), new);
                            rebuilt.set_span(group.span());
                            out.extend(std::iter::once(proc_macro2::TokenTree::Group(rebuilt)));
                        }
                        None => out.extend(std::iter::once(tree.clone())),
                    }
                }
                proc_macro2::TokenTree::Ident(ident) => {
                    match self.substitution_for(ident, &trees, index) {
                        Some((replacement, did_fold)) => {
                            folded |= did_fold;
                            marked |= !did_fold;
                            out.extend(replacement);
                        }
                        None => out.extend(std::iter::once(tree.clone())),
                    }
                }
                other => out.extend(std::iter::once(other.clone())),
            }
        }

        TokenRewrite::from_flags(out, folded, marked)
    }

    /// Substitute every registered name in `tokens` at every depth. Used only
    /// from the salvage floor; see [`Self::descend_stream`] for why it is sound
    /// in value position as well as pattern position.
    fn substitute_stream(
        &self,
        tokens: &proc_macro2::TokenStream,
    ) -> (proc_macro2::TokenStream, bool, bool) {
        let trees: Vec<proc_macro2::TokenTree> = tokens.clone().into_iter().collect();
        let mut out = proc_macro2::TokenStream::new();
        let mut folded = false;
        let mut marked = false;

        for (index, tree) in trees.iter().enumerate() {
            match tree {
                proc_macro2::TokenTree::Group(group) => {
                    let (inner, did_fold, did_mark) = self.substitute_stream(&group.stream());
                    folded |= did_fold;
                    marked |= did_mark;
                    let mut rebuilt = proc_macro2::Group::new(group.delimiter(), inner);
                    rebuilt.set_span(group.span());
                    out.extend(std::iter::once(proc_macro2::TokenTree::Group(rebuilt)));
                }
                proc_macro2::TokenTree::Ident(ident) => {
                    match self.substitution_for(ident, &trees, index) {
                        Some((replacement, did_fold)) => {
                            folded |= did_fold;
                            marked |= !did_fold;
                            out.extend(replacement);
                        }
                        None => out.extend(std::iter::once(tree.clone())),
                    }
                }
                other => out.extend(std::iter::once(other.clone())),
            }
        }

        (out, folded, marked)
    }

    /// The replacement for one identifier token, plus whether it was a FOLD
    /// (`true`) or the fail-closed MARK (`false`). `None` leaves the token alone.
    ///
    /// The neighbour tests are the narrowness pins on the salvage floor. They
    /// skip exactly the positions in which an identifier spelled like a const is
    /// provably NOT that const, so substituting there could only break working
    /// code:
    ///
    /// * `x.kk` — a field or method name;
    /// * `crate::kk`, `m::kk` — a trailing path segment, which resolves through
    ///   its qualifier and not through this file's bare-name registry;
    /// * `kk::x`, `kk: T`, `S { kk: v }` — a path ROOT (a module/type/enum, never
    ///   a const), a type-annotated binder, or a struct-literal field name.
    ///
    /// The leading test is deliberately `::` and NOT a single `:`. A lone
    /// preceding colon is the VALUE half of `S { field: kk }` — a position where
    /// a const pattern genuinely lives, and skipping it would leave exactly the
    /// bare ident that `arm_pattern_match_condition` answers `Always` for.
    fn substitution_for(
        &self,
        ident: &proc_macro2::Ident,
        trees: &[proc_macro2::TokenTree],
        index: usize,
    ) -> Option<(proc_macro2::TokenStream, bool)> {
        let name = ident.to_string();
        let value = self.consts.get(&name)?;

        let punct_at = |slot: usize| {
            trees.get(slot).and_then(|tree| match tree {
                proc_macro2::TokenTree::Punct(punct) => Some(punct.as_char()),
                _ => None,
            })
        };

        let prev = index.checked_sub(1).and_then(punct_at);
        if prev == Some('.') {
            return None;
        }
        // `:: kk` — a qualified path. `field : kk` is NOT one.
        if prev == Some(':') && index.checked_sub(2).and_then(punct_at) == Some(':') {
            return None;
        }
        // `kk !` (a macro name), `kk :` (binder annotation / struct-literal
        // field name) and `kk ::` (a path root) are all non-const positions.
        if matches!(punct_at(index + 1), Some('!') | Some(':')) {
            return None;
        }

        match value {
            ConstPatternValue::Literal(lit) => Some((quote!(#lit), true)),
            ConstPatternValue::Unmodeled => {
                let marker =
                    syn::Ident::new(&format!("{UNMODELED_CONST_PAT_PREFIX}{name}"), ident.span());
                Some((quote!(#marker), false))
            }
        }
    }

    /// Does any identifier anywhere in `tokens` name a registry entry?
    fn mentions_registered_name(&self, tokens: &proc_macro2::TokenStream) -> bool {
        tokens.clone().into_iter().any(|tree| match tree {
            proc_macro2::TokenTree::Ident(ident) => self.consts.contains_key(&ident.to_string()),
            proc_macro2::TokenTree::Group(group) => self.mentions_registered_name(&group.stream()),
            _ => false,
        })
    }
}

/// One piece of a token stream split at its top-level `,` / `;` separators.
enum Segment {
    Tokens(proc_macro2::TokenStream),
    Separator(proc_macro2::TokenTree),
}

/// Split at top-level `,` and `;`. Tokens inside a delimited group are not
/// top-level, so `match n { a, b }` stays one piece.
fn split_top_level(tokens: &proc_macro2::TokenStream) -> Vec<Segment> {
    let mut out: Vec<Segment> = Vec::new();
    let mut current = proc_macro2::TokenStream::new();
    let mut saw_separator = false;

    for tree in tokens.clone() {
        let is_separator = matches!(
            &tree,
            proc_macro2::TokenTree::Punct(punct)
                if matches!(punct.as_char(), ',' | ';')
                    && punct.spacing() == proc_macro2::Spacing::Alone
        );
        if is_separator {
            saw_separator = true;
            if !current.is_empty() {
                out.push(Segment::Tokens(std::mem::take(&mut current)));
            }
            out.push(Segment::Separator(tree));
        } else {
            current.extend(std::iter::once(tree));
        }
    }
    if !current.is_empty() {
        out.push(Segment::Tokens(current));
    }
    if !saw_separator {
        // One piece, identical to the input: report it as such so the caller
        // does not recurse on itself.
        return vec![Segment::Tokens(tokens.clone())];
    }
    out
}

/// The answer [`ConstPatternRewriter::rewrite_tokens`] gives about one
/// macro/attribute token stream.
///
/// The point of the enum is that its first two variants used to be the SAME
/// value (`None`). "Nothing to rewrite" and "cannot tell" are different facts
/// and only one of them is safe to ignore.
enum TokenRewrite {
    /// Nothing to rewrite, and that is established: either no registered name
    /// occurs anywhere in the stream, or the stream parsed and held no pattern
    /// naming one.
    Unchanged,
    /// A fold fired. These tokens replace the stream.
    Rewritten(proc_macro2::TokenStream),
    /// A registered name occurs somewhere this pass could not decide, so the
    /// carried tokens have it renamed to [`UNMODELED_CONST_PAT_PREFIX`] —
    /// which every downstream pattern lane rejects. The caller installs these
    /// tokens exactly as it installs a `Rewritten`, so the decline cannot be
    /// mistaken for "nothing to do here".
    Unresolved(proc_macro2::TokenStream),
}

impl TokenRewrite {
    fn into_tokens(self) -> Option<proc_macro2::TokenStream> {
        match self {
            TokenRewrite::Unchanged => None,
            TokenRewrite::Rewritten(tokens) | TokenRewrite::Unresolved(tokens) => Some(tokens),
        }
    }

    fn from_flags(tokens: proc_macro2::TokenStream, folded: bool, marked: bool) -> Self {
        if marked {
            TokenRewrite::Unresolved(tokens)
        } else if folded {
            TokenRewrite::Rewritten(tokens)
        } else {
            TokenRewrite::Unchanged
        }
    }
}

impl VisitMut for ConstPatternRewriter<'_> {
    fn visit_arm_mut(&mut self, arm: &mut syn::Arm) {
        self.rewrite_pat(&mut arm.pat);
        syn::visit_mut::visit_arm_mut(self, arm);
    }

    fn visit_expr_let_mut(&mut self, expr_let: &mut ExprLet) {
        self.rewrite_pat(&mut expr_let.pat);
        syn::visit_mut::visit_expr_let_mut(self, expr_let);
    }

    fn visit_local_mut(&mut self, local: &mut Local) {
        // ONLY `let PAT = init else { .. }` is a refutable position. A plain
        // `let` requires an irrefutable pattern, so a const name there is not
        // valid Rust (E0005) and is left alone rather than silently reshaped.
        if local
            .init
            .as_ref()
            .is_some_and(|init| init.diverge.is_some())
        {
            self.rewrite_pat(&mut local.pat);
        }
        syn::visit_mut::visit_local_mut(self, local);
    }

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        syn::visit_mut::visit_expr_mut(self, expr);
        if let Expr::Macro(expr_macro) = expr {
            // Both a fold and a fail-closed decline install tokens here; only
            // `Unchanged` leaves the stream alone.
            if let Some(new_tokens) = self.rewrite_tokens(&expr_macro.mac.tokens).into_tokens() {
                expr_macro.mac.tokens = new_tokens;
                self.rewrote = true;
            }
        }
    }

    fn visit_stmt_mut(&mut self, stmt: &mut Stmt) {
        syn::visit_mut::visit_stmt_mut(self, stmt);
        if let Stmt::Macro(stmt_macro) = stmt {
            if let Some(new_tokens) = self.rewrite_tokens(&stmt_macro.mac.tokens).into_tokens() {
                stmt_macro.mac.tokens = new_tokens;
                self.rewrote = true;
            }
        }
    }

    /// Signature patterns are never rewritten: a parameter is an irrefutable
    /// binding, and turning one into a literal would delete the parameter.
    fn visit_signature_mut(&mut self, _sig: &mut syn::Signature) {}
}

fn rewrite_contract_attrs(
    consts: &BTreeMap<String, ConstPatternValue>,
    attrs: &mut [Attribute],
) -> bool {
    let rewriter = ConstPatternRewriter {
        consts,
        rewrote: false,
    };
    let mut changed = false;
    for attr in attrs.iter_mut() {
        let Meta::List(meta_list) = &mut attr.meta else {
            continue;
        };
        let is_contract = meta_list.path.segments.last().is_some_and(|seg| {
            matches!(
                seg.ident.to_string().as_str(),
                "requires" | "ensures" | "recommends" | "invariant" | "decreases"
            )
        });
        if !is_contract {
            continue;
        }
        if let Some(new_tokens) = rewriter.rewrite_tokens(&meta_list.tokens).into_tokens() {
            meta_list.tokens = new_tokens;
            changed = true;
        }
    }
    changed
}

/// Is `func` an item of the file's own top-level scope — the only scope whose
/// `const`s and `use`s this pass can place?
///
/// Matched on the SIGNATURE tokens, not the name alone. A signature that also
/// occurs nested answers `false`: an ambiguous placement must fail closed, not
/// pick the reading that folds.
fn is_file_top_level_fn(file: &File, func: &syn::ItemFn) -> bool {
    let wanted = func.sig.to_token_stream().to_string();

    fn occurs_nested(items: &[Item], wanted: &str, top: bool) -> bool {
        items.iter().any(|item| match item {
            Item::Fn(f) => {
                (!top && f.sig.to_token_stream().to_string() == wanted)
                    || occurs_nested(
                        &f.block
                            .stmts
                            .iter()
                            .filter_map(|stmt| match stmt {
                                Stmt::Item(inner) => Some(inner.clone()),
                                _ => None,
                            })
                            .collect::<Vec<_>>(),
                        wanted,
                        false,
                    )
            }
            Item::Mod(m) => m
                .content
                .as_ref()
                .is_some_and(|(_, inner)| occurs_nested(inner, wanted, false)),
            _ => false,
        })
    }

    let at_top = file
        .items
        .iter()
        .any(|item| matches!(item, Item::Fn(f) if f.sig.to_token_stream().to_string() == wanted));

    at_top && !occurs_nested(&file.items, &wanted, true)
}

/// Rewrite every declared-`const`-name pattern in `func` (body, `assert!`
/// bodies, and contract attributes). Returns `Some(rewritten)` iff anything
/// changed.
pub(crate) fn desugar_const_patterns(
    func: &syn::ItemFn,
    file: Option<&File>,
) -> Option<syn::ItemFn> {
    let file = file?;
    let mut consts = collect_declared_consts(file);
    if consts.is_empty() {
        return None;
    }
    // A file-top-level `const K` is NOT in scope inside `mod inner` — Rust items
    // do not nest lexically — so inside a nested function a bare `K` is an
    // ordinary BINDER. Folding it there narrows the arm's path condition, which
    // is the false-verify direction, and it verified:
    //
    //     const K: u64 = 5;
    //     mod inner {
    //         #[trust_vc::requires(n < 100)]
    //         pub fn f(n: u64) { match n { K => { assert!(n == 5); } } }   // VERIFIED
    //     }
    //
    // Nested functions ARE verified, so the answer is to demote rather than
    // skip: for a function this pass cannot place at file scope, no value is
    // vouched for and every declared name goes to the fail-closed marker. A
    // nested function reaching the const legitimately (`use super::K`) loses the
    // fold and fails closed — the sound direction, and the direction this lane
    // already took before any const was folded at all.
    if !is_file_top_level_fn(file, func) {
        for value in consts.values_mut() {
            *value = ConstPatternValue::Unmodeled;
        }
    }
    // Cheap pre-check: no declared const name occurs anywhere in the function's
    // tokens, so no pattern can name one.
    let names: BTreeSet<&str> = consts.keys().map(String::as_str).collect();
    let text = func.to_token_stream().to_string();
    if !names.iter().any(|name| text.contains(*name)) {
        return None;
    }

    let mut rewritten = func.clone();
    let mut rewriter = ConstPatternRewriter {
        consts: &consts,
        rewrote: false,
    };
    rewriter.visit_item_fn_mut(&mut rewritten);
    let body_changed = rewriter.rewrote;
    let attrs_changed = rewrite_contract_attrs(&consts, &mut rewritten.attrs);
    (body_changed || attrs_changed).then_some(rewritten)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(src: &str) -> File {
        syn::parse_str(src).expect("parse file")
    }

    /// The named fn inside the named inline module, found BY NAME. Positional
    /// indexing is brittle here — an inner attribute is not an item — and got
    /// this wrong once already.
    fn fn_in_mod(file: &File, module: &str, func: &str) -> syn::ItemFn {
        let items = file
            .items
            .iter()
            .find_map(|item| match item {
                Item::Mod(m) if m.ident == module => Some(&m.content.as_ref().expect("inline").1),
                _ => None,
            })
            .expect("the module");
        items
            .iter()
            .find_map(|item| match item {
                Item::Fn(f) if f.sig.ident == func => Some(f.clone()),
                _ => None,
            })
            .expect("the fn")
    }

    fn only_fn(file: &File) -> &syn::ItemFn {
        file.items
            .iter()
            .find_map(|item| match item {
                Item::Fn(f) => Some(f),
                _ => None,
            })
            .expect("a fn item")
    }

    #[test]
    fn uppercase_top_level_const_pattern_folds_to_its_literal() {
        let file = parse("const K: u64 = 5; fn f(n: u64) { match n { K => {} _ => {} } }");
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        let text = out.to_token_stream().to_string();
        assert!(text.contains("5 =>"), "{text}");
        assert!(!text.contains("K =>"), "{text}");
    }

    #[test]
    fn lowercase_top_level_const_pattern_folds_to_its_literal() {
        let file = parse(
            "#![allow(non_upper_case_globals)] const kk: u64 = 5; \
             fn f(n: u64) { match n { kk => {} _ => {} } }",
        );
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        let text = out.to_token_stream().to_string();
        assert!(text.contains("5 =>"), "{text}");
    }

    /// THE CAPABILITY PIN. An ordinary lowercase binder that names NO declared
    /// const must keep binding — the overwhelmingly common case.
    #[test]
    fn ordinary_binder_is_untouched() {
        let file = parse("const K: u64 = 5; fn f(n: u64) -> u64 { match n { m => m } }");
        assert!(desugar_const_patterns(only_fn(&file), Some(&file)).is_none());
    }

    /// A binder whose name collides with an ASSOCIATED const still binds: a
    /// bare `k` never resolves to `S::k`.
    #[test]
    fn associated_const_does_not_capture_a_binder() {
        let file = parse(
            "struct S; impl S { const m: u64 = 5; } fn f(n: u64) -> u64 { match n { m => m } }",
        );
        assert!(desugar_const_patterns(only_fn(&file), Some(&file)).is_none());
    }

    /// A duplicated name must NOT fold to either value — it goes to the
    /// fail-closed marker.
    #[test]
    fn duplicate_declaration_is_never_folded() {
        let file = parse(
            "const K: u64 = 5; mod m { pub const K: u64 = 9; } \
             fn f(n: u64) { match n { K => {} _ => {} } }",
        );
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        let text = out.to_token_stream().to_string();
        assert!(text.contains(UNMODELED_CONST_PAT_PREFIX), "{text}");
        assert!(!text.contains("5 =>"), "{text}");
        assert!(!text.contains("9 =>"), "{text}");
    }

    #[test]
    fn non_literal_initializer_goes_to_the_marker() {
        let file = parse(
            "const A: u64 = 5; const B: u64 = A + 1; fn f(n: u64) { match n { B => {} _ => {} } }",
        );
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        assert!(out
            .to_token_stream()
            .to_string()
            .contains(UNMODELED_CONST_PAT_PREFIX));
    }

    #[test]
    fn ref_and_mut_bindings_are_never_reinterpreted() {
        let file =
            parse("const K: u64 = 5; fn f(n: u64) -> u64 { match n { ref K => 1, mut K => 2 } }");
        assert!(desugar_const_patterns(only_fn(&file), Some(&file)).is_none());
    }

    #[test]
    fn signature_patterns_are_never_rewritten() {
        let file = parse("const K: u64 = 5; fn f(K: u64) -> u64 { K }");
        assert!(desugar_const_patterns(only_fn(&file), Some(&file)).is_none());
    }

    #[test]
    fn plain_let_binding_is_not_a_refutable_position() {
        let file = parse("const K: u64 = 5; fn f(n: u64) -> u64 { let K = n; K }");
        assert!(desugar_const_patterns(only_fn(&file), Some(&file)).is_none());
    }

    #[test]
    fn let_else_pattern_is_rewritten() {
        let file =
            parse("const K: u64 = 5; fn f(n: u64) -> u64 { let K = n else { return 0 }; 7 }");
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        assert!(out.to_token_stream().to_string().contains("let 5 = n"));
    }

    #[test]
    fn nested_constructor_subpattern_is_rewritten() {
        let file =
            parse("const K: u64 = 5; fn f(o: Option<u64>) { match o { Some(K) => {} _ => {} } }");
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        assert!(out.to_token_stream().to_string().contains("Some (5)"));
    }

    #[test]
    fn struct_shorthand_field_gains_its_colon() {
        let file =
            parse("const K: u64 = 5; struct P { K: u64 } fn f(p: P) { match p { P { K } => {} } }");
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        let text = out.to_token_stream().to_string();
        assert!(text.contains("K : 5"), "{text}");
        // Re-parsing must succeed: a shorthand carrying a literal is invalid.
        let _: syn::ItemFn = syn::parse2(out.to_token_stream()).expect("reparse");
    }

    #[test]
    fn float_and_string_initializers_are_not_folded() {
        let file = parse("const F: f64 = 1.5; fn f(n: f64) { match n { F => {} _ => {} } }");
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        assert!(out
            .to_token_stream()
            .to_string()
            .contains(UNMODELED_CONST_PAT_PREFIX));
    }

    #[test]
    fn no_file_means_no_rewrite() {
        let file = parse("const K: u64 = 5; fn f(n: u64) { match n { K => {} _ => {} } }");
        assert!(desugar_const_patterns(only_fn(&file), None).is_none());
    }

    // ---- `use` aliases ----------------------------------------------------

    #[test]
    fn use_alias_of_a_top_level_const_folds_to_its_literal() {
        let file = parse(
            "#![allow(non_upper_case_globals)] const lower_k: u64 = 5; \
             use crate::lower_k as alias_k; \
             fn f(n: u64) { match n { alias_k => {} _ => {} } }",
        );
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        let text = out.to_token_stream().to_string();
        assert!(text.contains("5 =>"), "{text}");
        assert!(!text.contains("alias_k =>"), "{text}");
    }

    #[test]
    fn use_alias_of_a_nested_module_const_folds_to_its_literal() {
        let file = parse(
            "mod helpers { pub const MAXV: u64 = 9; } \
             use crate::helpers::MAXV as maxv; \
             fn f(n: u64) { match n { maxv => {} _ => {} } }",
        );
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        let text = out.to_token_stream().to_string();
        assert!(text.contains("9 =>"), "{text}");
    }

    #[test]
    fn self_rooted_use_resolves_like_crate() {
        let file = parse(
            "mod helpers { pub const MAXV: u64 = 9; } \
             use self::helpers::MAXV as maxv; \
             fn f(n: u64) { match n { maxv => {} _ => {} } }",
        );
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        assert!(out.to_token_stream().to_string().contains("9 =>"));
    }

    #[test]
    fn grouped_use_aliases_are_all_resolved() {
        let file = parse(
            "mod helpers { pub const A: u64 = 1; pub const B: u64 = 2; } \
             use crate::helpers::{A as aa, B as bb}; \
             fn f(n: u64) { match n { aa => {} bb => {} _ => {} } }",
        );
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        let text = out.to_token_stream().to_string();
        assert!(text.contains("1 =>") && text.contains("2 =>"), "{text}");
    }

    /// THE NARROWNESS PIN. Only CONST aliases may change behaviour: an import
    /// naming a fn/type/struct-with-fields leaves an ordinary BINDER, which is
    /// what `use std::cmp::min;` plus `match n { min => .. }` relies on.
    #[test]
    fn fn_type_and_struct_aliases_leave_a_binder_alone() {
        for import in [
            "use crate::helpers::helper as min;",
            "use crate::helpers::Scalar as min;",
            "use crate::helpers::Payload as min;",
            "use crate::helpers::Inner as min;",
            "use crate::helpers::Marker as min;",
        ] {
            let src = format!(
                "mod helpers {{ pub fn helper(x: u64) -> u64 {{ x }} \
                 pub type Scalar = u64; pub struct Payload {{ pub a: u64 }} \
                 pub mod Inner {{}} pub trait Marker {{}} }} \
                 {import} fn f(n: u64) -> u64 {{ match n {{ min => min }} }}"
            );
            let file = parse(&src);
            assert!(
                desugar_const_patterns(only_fn(&file), Some(&file)).is_none(),
                "{import} must leave `min` a binder"
            );
        }
    }

    /// A unit struct IS a refutable pattern, so an alias of one fails closed.
    #[test]
    fn unit_struct_alias_fails_closed() {
        let file = parse(
            "mod helpers { pub struct Unit; } use crate::helpers::Unit as unit_alias; \
             fn f(n: u64) { match n { unit_alias => {} _ => {} } }",
        );
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        assert!(out
            .to_token_stream()
            .to_string()
            .contains(UNMODELED_CONST_PAT_PREFIX));
    }

    #[test]
    fn out_of_line_module_import_fails_closed() {
        let file = parse(
            "mod out_of_line; use crate::out_of_line::k; \
             fn f(n: u64) { match n { k => {} _ => {} } }",
        );
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        assert!(out
            .to_token_stream()
            .to_string()
            .contains(UNMODELED_CONST_PAT_PREFIX));
    }

    #[test]
    fn external_and_super_rooted_imports_fail_closed() {
        for import in ["use other_crate::K as k;", "use super::K as k;"] {
            let src = format!("{import} fn f(n: u64) {{ match n {{ k => {{}} _ => {{}} }} }}");
            let file = parse(&src);
            let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
            assert!(
                out.to_token_stream()
                    .to_string()
                    .contains(UNMODELED_CONST_PAT_PREFIX),
                "{import} must fail closed"
            );
        }
    }

    /// A glob names no local, so it is skipped — failing closed on every binder
    /// in a `use vstd::prelude::*;` file would reject the corpus. A const the
    /// glob's module declares IN THIS FILE is still caught by `all_names`.
    #[test]
    fn glob_import_does_not_reject_unrelated_binders() {
        let file = parse(
            "use other_crate::prelude::*; const K: u64 = 5; \
             fn f(n: u64) -> u64 { match n { m => m } }",
        );
        assert!(desugar_const_patterns(only_fn(&file), Some(&file)).is_none());
    }

    /// A `use` inside an inline `mod` is in scope for that mod's functions,
    /// which are verified too. It must not be invisible — but the value is not
    /// folded, because this pass does not model scope.
    #[test]
    fn nested_module_use_alias_fails_closed_not_open() {
        let file = parse(
            "#![allow(non_upper_case_globals)] const lower_k: u64 = 5; \
             mod inner { use crate::lower_k as nested_alias; \
             pub fn f(n: u64) { match n { nested_alias => {} _ => {} } } }",
        );
        let inner_fn = fn_in_mod(&file, "inner", "f");
        let out = desugar_const_patterns(&inner_fn, Some(&file)).expect("rewrite");
        let text = out.to_token_stream().to_string();
        assert!(text.contains(UNMODELED_CONST_PAT_PREFIX), "{text}");
        assert!(!text.contains("5 =>"), "{text}");
    }

    /// A file-top-level const is not in scope inside a `mod`, so its name is an
    /// ordinary BINDER there and must not be folded.
    #[test]
    fn nested_fn_does_not_inherit_a_file_top_level_const() {
        let file = parse(
            "const K: u64 = 5; \
             mod inner { pub fn f(n: u64) -> u64 { match n { K => n } } }",
        );
        let inner_fn = fn_in_mod(&file, "inner", "f");
        let out = desugar_const_patterns(&inner_fn, Some(&file)).expect("rewrite");
        let text = out.to_token_stream().to_string();
        assert!(text.contains(UNMODELED_CONST_PAT_PREFIX), "{text}");
        assert!(!text.contains("5 =>"), "{text}");
    }

    /// THE CAPABILITY CONTROL for the scope gate: the same const in the same
    /// file still folds for a TOP-LEVEL function.
    #[test]
    fn top_level_fn_still_folds_with_a_nested_module_present() {
        let file = parse(
            "const K: u64 = 5; mod inner { pub fn g(x: u64) -> u64 { x } } \
             fn f(n: u64) -> u64 { match n { K => n } }",
        );
        let top = file
            .items
            .iter()
            .find_map(|item| match item {
                Item::Fn(f) if f.sig.ident == "f" => Some(f.clone()),
                _ => None,
            })
            .expect("top-level fn");
        let out = desugar_const_patterns(&top, Some(&file)).expect("rewrite");
        assert!(out.to_token_stream().to_string().contains("5 =>"));
    }

    /// The pin holds at nesting depth too: a nested fn import leaves a binder.
    #[test]
    fn nested_module_fn_alias_leaves_a_binder_alone() {
        let file = parse(
            "mod helpers { pub fn helper(x: u64) -> u64 { x } } \
             mod inner { use crate::helpers::helper as min; \
             pub fn f(n: u64) -> u64 { match n { min => min } } }",
        );
        let inner_fn = fn_in_mod(&file, "inner", "f");
        assert!(desugar_const_patterns(&inner_fn, Some(&file)).is_none());
    }

    #[test]
    fn alias_colliding_with_a_declared_name_fails_closed() {
        let file = parse(
            "mod a { pub const kk: u64 = 1; } mod b { pub const other: u64 = 2; } \
             use crate::b::other as kk; \
             fn f(n: u64) { match n { kk => {} _ => {} } }",
        );
        let out = desugar_const_patterns(only_fn(&file), Some(&file)).expect("rewrite");
        let text = out.to_token_stream().to_string();
        assert!(text.contains(UNMODELED_CONST_PAT_PREFIX), "{text}");
        assert!(!text.contains("1 =>") && !text.contains("2 =>"), "{text}");
    }

    // ---- SCOPE: every container that can hold a declaration ---------------
    //
    // The registry is only as good as the scopes it walks. Each case here
    // declares the const in a container the first collector never descended
    // into and asserts the name reached the registry — the marker in the
    // rewritten output is the evidence, since an uncollected name is left
    // untouched and `desugar_const_patterns` returns `None`.

    /// Assert that `src` puts `name` in the registry: the pattern naming it is
    /// rewritten to the fail-closed marker rather than left as a binder.
    fn assert_collected(src: &str, label: &str) {
        let file = parse(src);
        // BY NAME, never `only_fn`: several of these sources declare the const
        // inside a top-level `fn g`, which is the FIRST `Item::Fn` in the file.
        let probe = top_fn(&file, "f");
        let out = desugar_const_patterns(&probe, Some(&file)).unwrap_or_else(|| {
            panic!("{label}: nothing rewritten — the declaration was invisible")
        });
        let text = out.to_token_stream().to_string();
        assert!(text.contains(UNMODELED_CONST_PAT_PREFIX), "{label}: {text}");
    }

    /// The named FILE-TOP-LEVEL fn.
    fn top_fn(file: &File, name: &str) -> syn::ItemFn {
        file.items
            .iter()
            .find_map(|item| match item {
                Item::Fn(f) if f.sig.ident == name => Some(f.clone()),
                _ => None,
            })
            .unwrap_or_else(|| panic!("top-level fn `{name}`"))
    }

    const PROBE_FN: &str = "fn f(n: u64) { match n { buried => {} _ => {} } }";

    #[test]
    fn const_in_an_impl_method_body_is_collected() {
        assert_collected(
            &format!(
                "#![allow(non_upper_case_globals)] struct S; \
                 impl S {{ fn g() -> u64 {{ const buried: u64 = 5; buried }} }} {PROBE_FN}"
            ),
            "impl method body",
        );
    }

    #[test]
    fn const_in_a_trait_default_method_body_is_collected() {
        assert_collected(
            &format!(
                "#![allow(non_upper_case_globals)] \
                 trait T {{ fn g() -> u64 {{ const buried: u64 = 5; buried }} }} {PROBE_FN}"
            ),
            "trait default body",
        );
    }

    #[test]
    fn const_in_a_nested_block_is_collected() {
        assert_collected(
            &format!(
                "#![allow(non_upper_case_globals)] \
                 fn g() -> u64 {{ {{ const buried: u64 = 5; buried }} }} {PROBE_FN}"
            ),
            "nested block",
        );
    }

    /// The shape an `Item::Impl`/`Item::Trait` patch alone would still miss.
    #[test]
    fn const_in_a_nested_block_inside_an_impl_method_is_collected() {
        assert_collected(
            &format!(
                "#![allow(non_upper_case_globals)] struct S; \
                 impl S {{ fn g() -> u64 {{ {{ const buried: u64 = 5; buried }} }} }} {PROBE_FN}"
            ),
            "nested block inside an impl method",
        );
    }

    #[test]
    fn const_in_a_const_initializer_block_is_collected() {
        assert_collected(
            &format!(
                "#![allow(non_upper_case_globals)] \
                 const OUTER: u64 = {{ const buried: u64 = 5; buried }}; {PROBE_FN}"
            ),
            "const initializer block",
        );
    }

    #[test]
    fn static_in_an_impl_method_body_is_collected() {
        assert_collected(
            &format!(
                "#![allow(non_upper_case_globals)] struct S; \
                 impl S {{ fn g() -> u64 {{ static buried: u64 = 5; buried }} }} {PROBE_FN}"
            ),
            "impl method body (static)",
        );
    }

    #[test]
    fn use_alias_in_an_impl_method_body_is_collected() {
        assert_collected(
            &format!(
                "#![allow(non_upper_case_globals)] const src: u64 = 5; struct S; \
                 impl S {{ fn g() -> u64 {{ use crate::src as buried; buried }} }} {PROBE_FN}"
            ),
            "impl method body (use alias)",
        );
    }

    #[test]
    fn use_alias_in_a_nested_block_is_collected() {
        assert_collected(
            &format!(
                "#![allow(non_upper_case_globals)] const src: u64 = 5; \
                 fn g() -> u64 {{ {{ use crate::src as buried; buried }} }} {PROBE_FN}"
            ),
            "nested block (use alias)",
        );
    }

    #[test]
    fn use_alias_in_a_trait_default_method_body_is_collected() {
        assert_collected(
            &format!(
                "#![allow(non_upper_case_globals)] const src: u64 = 5; \
                 trait T {{ fn g() -> u64 {{ use crate::src as buried; buried }} }} {PROBE_FN}"
            ),
            "trait default body (use alias)",
        );
    }

    /// THE NARROWNESS PIN for the whole-tree walk. Descending into `impl` and
    /// `trait` bodies must NOT start collecting ASSOCIATED consts — a bare `m`
    /// never resolves to `S::m`, so collecting one converts a genuine BINDER
    /// into a fail-closed marker. They stay excluded because `ImplItemConst`
    /// and `TraitItemConst` are different syn nodes, not because an arm omits
    /// them.
    #[test]
    fn associated_consts_are_still_excluded_at_every_depth() {
        for decl in [
            "struct S; impl S { const m: u64 = 5; }",
            "trait T { const m: u64 = 5; }",
            "trait T { const m: u64; } struct S; impl T for S { const m: u64 = 5; }",
            "mod inner { pub struct S; impl S { pub const m: u64 = 5; } }",
        ] {
            let src = format!("{decl} fn f(n: u64) -> u64 {{ match n {{ m => m }} }}");
            let file = parse(&src);
            let probe = top_fn(&file, "f");
            assert!(
                desugar_const_patterns(&probe, Some(&file)).is_none(),
                "{decl} must leave `m` a binder"
            );
        }
    }

    /// THE CAPABILITY PIN for the collector's top-level `use` bookkeeping. The
    /// whole-tree scan sees every `use`; if it saw the FILE-SCOPE ones too they
    /// would be entered twice and `enter_alias` would demote each to the
    /// fail-closed marker, silently retiring the alias fold.
    #[test]
    fn file_scope_use_alias_still_folds_with_nested_scopes_present() {
        let file = parse(
            "#![allow(non_upper_case_globals)] const lower_k: u64 = 5; \
             use crate::lower_k as alias_k; \
             struct S; impl S { fn g() -> u64 { { let z = 1; z } } } \
             fn f(n: u64) { match n { alias_k => {} _ => {} } }",
        );
        let top = top_fn(&file, "f");
        let out = desugar_const_patterns(&top, Some(&file)).expect("rewrite");
        let text = out.to_token_stream().to_string();
        assert!(text.contains("5 =>"), "{text}");
        assert!(!text.contains(UNMODELED_CONST_PAT_PREFIX), "{text}");
    }

    /// A file-scope alias and a same-named alias in a nested scope are two
    /// spellings this pass cannot tell apart, so neither is folded.
    #[test]
    fn nested_alias_colliding_with_a_file_scope_alias_fails_closed() {
        let file = parse(
            "#![allow(non_upper_case_globals)] const a: u64 = 1; const b: u64 = 2; \
             use crate::a as alias_k; \
             struct S; impl S { fn g() -> u64 { use crate::b as alias_k; alias_k } } \
             fn f(n: u64) { match n { alias_k => {} _ => {} } }",
        );
        let top = top_fn(&file, "f");
        let out = desugar_const_patterns(&top, Some(&file)).expect("rewrite");
        let text = out.to_token_stream().to_string();
        assert!(text.contains(UNMODELED_CONST_PAT_PREFIX), "{text}");
        assert!(!text.contains("1 =>") && !text.contains("2 =>"), "{text}");
    }

    /// THE NARROWNESS PIN, stated the other way: an ordinary binder naming
    /// nothing declared anywhere in the file is untouched no matter how many
    /// scopes the walk now visits.
    #[test]
    fn ordinary_binder_survives_the_whole_tree_walk() {
        let file = parse(
            "#![allow(non_upper_case_globals)] const K: u64 = 5; struct S; \
             impl S { fn g() -> u64 { { const buried: u64 = 7; buried } } } \
             trait T { fn h() -> u64 { const other: u64 = 9; other } } \
             fn f(n: u64) -> u64 { match n { m => m } }",
        );
        let top = top_fn(&file, "f");
        assert!(desugar_const_patterns(&top, Some(&file)).is_none());
    }

    // ---- MACRO GRAMMAR: every supported body macro, not just `Expr` --------
    //
    // `rewrite_tokens` is the ONLY path by which this pass reaches a pattern
    // inside a macro. Its predecessor parsed the stream as one `syn::Expr` and
    // answered `None` otherwise — the same value it answers when nothing needs
    // rewriting — so every supported macro with a non-`Expr` grammar skipped
    // the desugar in silence and reproduced the original cardinal false verify.
    // Measured at the CLI before the fix, `#[requires(n == 7)]` over
    // `pub const kk: u64 = 5u64`:
    //
    //     assert_eq!(match n { kk => 1u64, _ => 2u64 }, 1u64)        VERIFIED
    //     assert_ne!(..., 2u64)                                      VERIFIED
    //     assert_by!(... == 1u64, { })                               VERIFIED
    //     assert_by_contradiction!(... == 1u64, { })                 VERIFIED
    //     calc! { (==) ...; == { } 1u64; }                           VERIFIED
    //     assert!(... == 1u64)                        counterexample (the one
    //                                                  shape that already
    //                                                  parsed as an `Expr`)
    //
    // All five now refute. The table below pins the desugar's own output for
    // the WHOLE handled-macro list at `body_extract.rs::
    // is_supported_body_macro_name`, so a macro added there without a grammar
    // here shows up as a silent skip rather than as a false verify months
    // later.

    /// `pub fn f(n: u64) { BODY }` beneath a foldable file-top-level const.
    fn probe_body(body: &str) -> String {
        let src = format!(
            "#![allow(non_upper_case_globals)] pub const kk: u64 = 5u64; \
             pub fn f(n: u64) {{ {body} }}"
        );
        let file = parse(&src);
        let func = top_fn(&file, "f");
        match desugar_const_patterns(&func, Some(&file)) {
            Some(out) => out.to_token_stream().to_string(),
            None => func.to_token_stream().to_string(),
        }
    }

    /// A `match n { kk => .. }` arm, spelled inside each macro's own grammar.
    const CONST_ARM: &str = "match n { kk => 1u64, _ => 2u64 }";

    #[test]
    fn every_supported_body_macro_reaches_the_const_pattern() {
        // (label, body). Covers `is_supported_body_macro_name` in full, plus
        // `assert_by!` and `proof_block!`, which the same dispatch handles.
        let cases: Vec<(&str, String)> = vec![
            ("assert", format!("assert!({CONST_ARM} == 1u64);")),
            ("assume", format!("assume!({CONST_ARM} == 1u64);")),
            ("invariant", format!("invariant!({CONST_ARM} == 1u64);")),
            (
                "invariant_except_break",
                format!("invariant_except_break!({CONST_ARM} == 1u64);"),
            ),
            (
                "loop_ensures",
                format!("loop_ensures!({CONST_ARM} == 1u64);"),
            ),
            ("loop_decreases", format!("loop_decreases!({CONST_ARM});")),
            ("assert_eq", format!("assert_eq!({CONST_ARM}, 1u64);")),
            ("assert_ne", format!("assert_ne!({CONST_ARM}, 2u64);")),
            (
                "assert_seqs_equal",
                format!("assert_seqs_equal!(s, t, i => {CONST_ARM});"),
            ),
            (
                "calc",
                format!("calc! {{ (==) {CONST_ARM}; == {{ }} 1u64; }}"),
            ),
            (
                "assert_forall_by",
                format!("assert_forall_by!(|i: u64| {CONST_ARM} == 1u64 by {{ }});"),
            ),
            (
                "assert_by_nonlinear",
                format!("assert_by_nonlinear!({CONST_ARM} == 1u64 by {{ }});"),
            ),
            (
                "assert_by_bit_vector",
                format!("assert_by_bit_vector!({CONST_ARM} == 1u64 by {{ }});"),
            ),
            (
                "assert_by_compute",
                format!("assert_by_compute!({CONST_ARM} == 1u64);"),
            ),
            (
                "assert_by_contradiction",
                format!("assert_by_contradiction!({CONST_ARM} == 1u64, {{ }});"),
            ),
            (
                "assert_by",
                format!("assert_by!({CONST_ARM} == 1u64, {{ }});"),
            ),
            (
                "debug_assert",
                format!("debug_assert!({CONST_ARM} == 1u64);"),
            ),
            (
                "debug_assert_eq",
                format!("debug_assert_eq!({CONST_ARM}, 1u64);"),
            ),
            (
                "debug_assert_ne",
                format!("debug_assert_ne!({CONST_ARM}, 2u64);"),
            ),
            (
                "proof_block",
                format!("proof_block!({{ assert!({CONST_ARM} == 1u64); }});"),
            ),
        ];

        for (label, body) in cases {
            let text = probe_body(&body);
            assert!(
                !text.contains("kk =>"),
                "{label}!(): the const arm was SILENTLY SKIPPED — \
                 `arm_pattern_match_condition` will answer `Always` and \
                 vacuously discharge the sibling arm: {text}"
            );
            assert!(
                text.contains("5u64 =>") || text.contains(UNMODELED_CONST_PAT_PREFIX),
                "{label}!(): neither folded nor marked: {text}"
            );
        }
    }

    /// `reveal!`/`hide!`/`broadcast_use!` name a FUNCTION, not an expression.
    /// Nothing in them can be a pattern, and the mention gate says so without
    /// parsing — the "not reachable" row of the table.
    #[test]
    fn name_only_macros_are_left_alone() {
        for body in ["reveal!(g);", "hide!(g);", "broadcast_use!(lemma_x);"] {
            let text = probe_body(body);
            assert!(!text.contains(UNMODELED_CONST_PAT_PREFIX), "{body}: {text}");
            assert!(!text.contains("5u64"), "{body}: {text}");
        }
    }

    /// THE CAPABILITY PIN that a blunter fix fails: an ordinary lowercase
    /// BINDER inside every one of those macros must still BIND. A fix that
    /// blanket-marked unparseable streams, or that keyed on macro NAME and
    /// mangled the arm, turns `match n { m => m }` into a rejection here.
    #[test]
    fn an_ordinary_binder_inside_every_macro_still_binds() {
        let binder_arm = "match n { m => m }";
        for body in [
            format!("assert!({binder_arm} == 1u64);"),
            format!("assert_eq!({binder_arm}, 1u64);"),
            format!("assert_ne!({binder_arm}, 2u64);"),
            format!("assert_seqs_equal!(s, t, i => {binder_arm});"),
            format!("calc! {{ (==) {binder_arm}; == {{ }} 1u64; }}"),
            format!("assert_forall_by!(|i: u64| {binder_arm} == 1u64 by {{ }});"),
            format!("assert_by_bit_vector!({binder_arm} == 1u64 by {{ }});"),
            format!("assert_by_contradiction!({binder_arm} == 1u64, {{ }});"),
            format!("assert_by!({binder_arm} == 1u64, {{ }});"),
            format!("proof_block!({{ assert!({binder_arm} == 1u64); }});"),
        ] {
            let text = probe_body(&body);
            assert!(text.contains("m => m"), "{body}: binder lost: {text}");
            assert!(!text.contains(UNMODELED_CONST_PAT_PREFIX), "{body}: {text}");
        }
    }

    /// THE CAPABILITY PIN for the already-working shape: a const pattern in a
    /// plain `assert!` still folds and still selects the right arm. This is the
    /// route that was correct before the fix, and the cascade must not have
    /// re-routed it through the salvage floor.
    #[test]
    fn const_pattern_in_a_plain_assert_still_folds() {
        let text = probe_body(&format!("assert!({CONST_ARM} == 1u64);"));
        assert!(text.contains("5u64 =>"), "{text}");
        assert!(text.contains("_ => 2u64"), "{text}");
        assert!(!text.contains(UNMODELED_CONST_PAT_PREFIX), "{text}");
    }

    /// THE NARROWNESS PIN for `assert_eq!`: a non-const expression argument is
    /// untouched, byte for byte.
    #[test]
    fn a_non_const_expression_inside_assert_eq_is_unaffected() {
        for body in [
            "assert_eq!(n + 1u64, 8u64);",
            "assert_eq!(n, 7u64, \"message\");",
            "assert_ne!(n * 2u64, 0u64);",
        ] {
            let text = probe_body(body);
            assert!(!text.contains(UNMODELED_CONST_PAT_PREFIX), "{body}: {text}");
            assert!(!text.contains("5u64 =>"), "{body}: {text}");
        }
    }

    /// A const used as a VALUE — not a pattern — is left alone in every stream
    /// the cascade can parse. `assert_eq!(kk, 5u64)` is comma-separated, so the
    /// old single-`Expr` route could not even see it; the salvage floor WOULD
    /// substitute it. Route R2 keeps it exact.
    #[test]
    fn a_const_value_argument_is_not_a_pattern() {
        let text = probe_body("assert_eq!(kk, 5u64);");
        assert!(text.contains("kk"), "{text}");
        assert!(!text.contains(UNMODELED_CONST_PAT_PREFIX), "{text}");
    }

    /// THE NARROWNESS PIN for the spec-surface recognizer (cascade step R4).
    /// `==>` is not Rust, so no `syn` route parses this stream; without the
    /// recognizer it falls to the salvage floor and the const VALUE is
    /// substituted. Measured: with R4 disabled the same source comes back as
    /// `assert_by_bit_vector!(5u64 == 5u64 ==> ..)`, and the `Unmodeled` case
    /// below comes back MARKED — i.e. a working value use is broken.
    #[test]
    fn a_const_value_in_verus_surface_syntax_is_left_alone() {
        let text = probe_body("assert_by_bit_vector!(kk == 5u64 ==> n == n);");
        assert!(
            text.contains("kk == 5u64"),
            "R4 recognizer bypassed: {text}"
        );
        assert!(!text.contains(UNMODELED_CONST_PAT_PREFIX), "{text}");
    }

    /// The same pin with an UNMODELED entry, where the salvage floor's answer
    /// is a fail-closed MARK rather than a value-preserving fold — so this is
    /// the version where losing R4 costs real capability.
    #[test]
    fn an_unmodeled_const_value_in_verus_surface_syntax_is_left_alone() {
        let src = "#![allow(non_upper_case_globals)] pub const kk: u64 = 2u64 + 3u64; \
                   pub fn f(n: u64) { assert_by_bit_vector!(kk == 5u64 ==> n == n); }";
        let file = parse(src);
        let func = top_fn(&file, "f");
        assert!(
            desugar_const_patterns(&func, Some(&file)).is_none(),
            "an unparseable-but-recognized spec expression must not be marked"
        );
    }

    /// THE FAIL-CLOSED PIN. A pattern that the cascade cannot place — a const
    /// name nested inside a tuple-struct pattern in a `calc!` step, whose arm
    /// list parses as no Rust grammar at all — must not come back unchanged.
    /// This is the shape that separates `Unchanged` from `Unresolved`: an
    /// `Option<TokenStream>` cannot express it, which is why the return type
    /// changed.
    #[test]
    fn a_nested_const_pattern_in_an_unparseable_stream_is_still_reached() {
        let text =
            probe_body("calc! { (==) match q { Some(kk) => 1u64, _ => 2u64 }; == { } 1u64; }");
        assert!(
            !text.contains("Some (kk)") && !text.contains("Some(kk)"),
            "{text}"
        );
        assert!(
            text.contains("5u64") || text.contains(UNMODELED_CONST_PAT_PREFIX),
            "{text}"
        );
    }

    /// The VALUE half of a struct-pattern field is a const-pattern position, so
    /// the salvage floor's qualified-path skip must test `::` and not a lone
    /// `:`. Testing a lone `:` leaves `S { field: kk }` a bare ident — which is
    /// the `Always` classification this whole pass exists to prevent — while the
    /// FIELD NAME half (`S { kk: 5 }`) must still be skipped.
    #[test]
    fn a_struct_pattern_field_value_is_substituted_but_its_name_is_not() {
        let value_half = probe_body(
            "calc! { (==) match q { S { field: kk } => 1u64, _ => 2u64 }; == { } 1u64; }",
        );
        assert!(!value_half.contains("field : kk"), "{value_half}");
        assert!(value_half.contains("5u64"), "{value_half}");

        let name_half = probe_body(
            "calc! { (==) match q { S { kk: 1u64 } => 1u64, _ => 2u64 }; == { } 1u64; }",
        );
        assert!(
            name_half.contains("kk : 1u64"),
            "field NAME rewritten: {name_half}"
        );
    }

    /// A qualified path is never the bare name this registry keys on.
    #[test]
    fn qualified_paths_are_not_substituted_on_the_salvage_floor() {
        for body in [
            "calc! { (==) match q { m::kk => 1u64, _ => 2u64 }; == { } 1u64; }",
            "calc! { (==) match q { kk::V => 1u64, _ => 2u64 }; == { } 1u64; }",
        ] {
            let text = probe_body(body);
            assert!(text.contains("kk"), "{body}: {text}");
            assert!(!text.contains("5u64 =>"), "{body}: {text}");
        }
    }

    /// The `Unmodeled` half of the same shape: the marker, not a guess.
    #[test]
    fn an_unmodeled_name_in_an_unparseable_stream_is_marked() {
        let src = "#![allow(non_upper_case_globals)] pub const kk: u64 = 2u64 + 3u64; \
                   pub fn f(n: u64) { calc! { (==) match n { kk => 1u64, _ => 2u64 }; == { } 1u64; } }";
        let file = parse(src);
        let func = top_fn(&file, "f");
        let text = desugar_const_patterns(&func, Some(&file))
            .expect("an undecidable const name must not pass through silently")
            .to_token_stream()
            .to_string();
        assert!(text.contains(UNMODELED_CONST_PAT_PREFIX), "{text}");
    }

    /// A macro stream this pass has no business touching stays byte-identical
    /// as long as it names nothing in the registry — the gate that keeps the
    /// salvage floor away from `println!`, `vec![]`, `seq![]` and friends.
    #[test]
    fn unrelated_macro_streams_are_never_entered() {
        for body in [
            "println!(\"{} {}\", n, n + 1u64);",
            "let v = vec![1u64, 2u64, 3u64];",
            "let s = seq![n => n];",
        ] {
            let text = probe_body(body);
            assert!(!text.contains(UNMODELED_CONST_PAT_PREFIX), "{body}: {text}");
            assert!(!text.contains("5u64"), "{body}: {text}");
        }
    }

    #[test]
    fn marker_name_round_trips() {
        assert_eq!(
            unmodeled_const_pat_name(&format!("{UNMODELED_CONST_PAT_PREFIX}K")),
            Some("K")
        );
        assert_eq!(unmodeled_const_pat_name("K"), None);
    }
}
