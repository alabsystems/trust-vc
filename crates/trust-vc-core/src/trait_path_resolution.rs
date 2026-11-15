//! Resolving the trait path in `impl <Trait> for <Type>` to the trait
//! DECLARATION it actually names.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # Why this exists
//!
//! Every trait registry in the engine — `TraitDecl::name`, `ImplMethodKey`,
//! `TraitBound::trait_name`, `TraitDecl::supertraits`, the trait-method
//! self-receiver-kind map, the source trait contract registry — is keyed by a
//! trait's BARE IDENT. The producer of that key used to be
//! `trait_path.segments.last()`: the last segment of whatever path the `impl`
//! header wrote. That is not the trait; it is one syllable of a name for it.
//!
//! Two measured consequences, both on programs stock `rustc` compiles and runs:
//!
//! * **Wrong-trait, cardinal.** With `mod decoy { trait Tr { ensures(true) } }`
//!   textually ahead of `mod real { trait Tr { ensures(result == 1) } }`, the
//!   conformance lookup `trait_decls.iter().find(|d| d.name == "Tr")` answered
//!   with `decoy::Tr`. `impl real::Tr for S { fn m(&self) -> u64 { 99 } }` —
//!   which violates `real::Tr` — was reported `verified`. Flip the decoy's
//!   clause to `result == 2` and a CONFORMING body is refuted instead: the
//!   false claim verifies and the true claim is refuted, simultaneously.
//! * **Renamed import, fail-closed.** `use inner::Orig as Alias;` +
//!   `impl Alias for T` hard-errored "missing trait declaration 'Alias'",
//!   because the last segment is the RENAME, and no declaration bears it.
//!
//! # Shape of the fix
//!
//! Dropping the offending entry is NOT the remedy here: when competing
//! declarations exist, dropping the one the program named promotes the one it
//! did not. So resolution is made total and its ambiguity UNREPRESENTABLE:
//!
//! 1. [`TraitScopeIndex::reject_duplicate_trait_names`] fails the whole file
//!    closed when two `trait` items anywhere in it share a bare ident. Bare-name
//!    keying cannot represent that file, so no consumer is allowed to try.
//!    This is unconditional over every `trait` item — `#[trust_vc::trait_spec]`
//!    or not — because the self-receiver-kind registry keys unannotated traits
//!    too.
//!
//! 1a. [`prune_shadowed_duplicate_traits`] runs BEFORE that gate and is what
//!    keeps it from costing legal programs. Two same-named traits in different
//!    modules is legal Rust (`rustc --edition 2021` compiles and runs it), and
//!    `impl real::Tr for S` is NOT ambiguous — the qualifier names exactly one
//!    declaration. The pass resolves every site that NAMES a trait — impl
//!    headers, trait bounds, supertraits, `dyn`/`impl Trait` positions and
//!    `where` predicates — and, when all of them agree on ONE declaration of a
//!    duplicated ident, DELETES the same-named declarations nothing names. The
//!    gate above then passes because the file genuinely has unique trait idents
//!    — the invariant is RESTORED, not waived, so every bare-name-keyed consumer
//!    downstream (trait bounds, supertraits, the receiver-kind map,
//!    `trait_method_declares_requires`, the parameterized-trait shape probes)
//!    keeps the exact protection it had.
//!    Anything the pass cannot decide — a bare `impl Tr for S` or `T: Tr` with
//!    two candidates, two naming sites resolving to two different declarations,
//!    or a bound whose last segment is a duplicated ident but which resolves to
//!    no in-file declaration at all — is still rejected outright. Making a bound
//!    VOTE rather than rejecting it is what closed the measured cardinal in
//!    [`prune_shadowed_duplicate_traits`]'s "every naming site votes" section:
//!    with the impl naming `decoy::Tr` and the bound naming `real::Tr`, the
//!    bound's `"Tr"` was answered by the impl's survivor, so a FALSE assertion
//!    verified while its TRUE twin did not.
//!
//! 1b. [`TraitScopeIndex::reject_duplicate_type_names`] does the same on the
//!    RECEIVER side, and closes a separate cardinal false verify. All method
//!    metadata (`ctx.inherent_methods`, and the concrete trait-impl
//!    registration in `prepared_context::type_env`) is keyed by the self
//!    type's bare ident, and the trait-impl pass runs last and defers to any
//!    existing binding because "an inherent method shadows a trait method, as
//!    in Rust". True within one type; with the module path erased it also lets
//!    an inherent `v` on `inner::S` outrank the trait `v` of a DIFFERENT
//!    top-level `S`. Measured on a program stock `rustc` compiles and runs
//!    (`inner::S::v() == 1`, top-level `S::v() == 2`): `assert!(s.v() == 1)`
//!    VERIFIED and `assert!(s.v() == 2)` was refuted — the same simultaneous
//!    inversion as the trait case.
//! 2. [`TraitScopeIndex::resolve_impl_trait_path`] resolves an impl header's
//!    path through `use` renames, `pub use` re-export chains, nested module
//!    paths, `crate`/`self`/`super` qualifiers and glob imports, and answers
//!    with the DECLARATION's ident.
//! 3. Anything it cannot decide is an error, never a guess. In particular a
//!    path that resolves to NO in-file trait is only allowed to keep its last
//!    segment when that segment matches no in-file trait declaration —
//!    otherwise the old code would have matched a declaration the program does
//!    not name.
//!
//! Step 1 is what makes step 2 safe to key by bare ident: after it, a bare
//! ident denotes at most one in-file trait.

use std::collections::{BTreeMap, BTreeSet};

use crate::error::{TrustVcError, TrustVcResult};

const RESOLUTION_CONTEXT: &str = "resolve trait impl header";

/// Bound on `use`-chain following, so a cyclic or pathological re-export chain
/// terminates as UNDECIDABLE rather than recursing forever.
const MAX_USE_CHAIN_DEPTH: usize = 16;

/// What an `impl <path> for T` header's trait path denotes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TraitPathResolution {
    /// Exactly one in-file `trait` item. The payload is that DECLARATION's
    /// ident, which is what every bare-name registry must be keyed by.
    Declared(String),
    /// No in-file `trait` item, AND the path's last segment collides with no
    /// in-file trait declaration — so keeping the last segment as the key
    /// cannot answer with the wrong declaration. Downstream keeps its existing
    /// behaviour for a trait this file does not declare (a hard error for a
    /// concrete self type, a skip for an opaque one).
    Foreign(String),
    /// Competing or undecidable. The caller must fail the file CLOSED.
    Undecidable(String),
}

/// Every trait declaration, `use` binding, glob and module the file contains,
/// indexed by module path so a path can be resolved from the scope that wrote
/// it.
#[derive(Debug, Default)]
pub(crate) struct TraitScopeIndex {
    /// `(module path, ident)` for EVERY `trait` item in the file, annotated or
    /// not — an unannotated declaration still occupies the name.
    traits: BTreeSet<(Vec<String>, String)>,
    /// Bare idents of all in-file trait declarations, for the collision guard.
    trait_idents: BTreeSet<String>,
    /// `(module, in-scope name) -> path segments as written` for each explicit
    /// `use` binding (`use a::b::C;`, `use a::C as D;`, groups, `pub use`).
    use_bindings: BTreeMap<(Vec<String>, String), Vec<String>>,
    /// `(module, name)` bound by more than one `use` in the same module. Rust
    /// rejects that; we must not pick one.
    conflicting_use_bindings: BTreeSet<(Vec<String>, String)>,
    /// `module -> glob prefixes as written` (`use inner::*;`).
    glob_prefixes: BTreeMap<Vec<String>, Vec<Vec<String>>>,
    /// Module paths whose body is present in this file (inline `mod m { .. }`).
    inline_modules: BTreeSet<Vec<String>>,
    /// `(module path, ident)` for EVERY module-level `struct`/`enum`/`union` in
    /// the file. The method-metadata registry is keyed by the receiver type's
    /// BARE name, so two type declarations sharing one ident are as
    /// unrepresentable as two same-named traits — see
    /// [`TraitScopeIndex::reject_duplicate_type_names`].
    types: BTreeSet<(Vec<String>, String)>,
}

impl TraitScopeIndex {
    /// Indexes `file` once. Cheap enough to build per verification target.
    #[must_use]
    pub(crate) fn build(file: &syn::File) -> Self {
        let mut index = Self::default();
        index.collect_items(&file.items, &mut Vec::new());
        index
    }

    /// Fails the file CLOSED when two `trait` items share a bare ident.
    ///
    /// Not a stylistic rule: every trait registry in the engine is keyed by the
    /// bare ident, so such a file has no faithful representation. Answering
    /// "the first one" is the cardinal wrong-trait false verify this module's
    /// header records. Erroring is the fail-closed direction and it is exact —
    /// the file is named, along with both module paths.
    pub(crate) fn reject_duplicate_trait_names(&self) -> TrustVcResult<()> {
        let mut seen: BTreeMap<&str, &Vec<String>> = BTreeMap::new();
        for (module, name) in &self.traits {
            if let Some(previous) = seen.insert(name.as_str(), module) {
                return Err(TrustVcError::Encoding {
                    context: RESOLUTION_CONTEXT,
                    detail: format!(
                        "two traits in this file are both named `{name}` ({} and {}); trait \
                         registration is keyed by the trait's bare name, so the two declarations \
                         are indistinguishable and neither can be verified — rename one",
                        render_module(previous),
                        render_module(module),
                    ),
                });
            }
        }
        Ok(())
    }

    /// Fails the file CLOSED when two module-level type items share a bare ident.
    ///
    /// The exact type-side counterpart of [`Self::reject_duplicate_trait_names`],
    /// and it closes a CARDINAL false verify that the trait gate does not cover.
    /// `prepared_context::type_env` keys ALL method metadata by the receiver
    /// type's BARE name: `ctx.inherent_methods` is a
    /// `HashMap<(self_type, method_name), _>` whose `self_type` is the impl's
    /// self ident with no module path, and
    /// `register_trait_impl_methods_for_concrete_types` keys the same way.
    ///
    /// `register_method_metadata` does guard a same-key conflict, but only
    /// between two entries that BOTH reach it — and the concrete trait-impl pass
    /// runs LAST and is deliberately fail-safe: it "never overrides an existing
    /// binding", justified by "inherent methods shadow trait methods, as in
    /// Rust". That justification holds only when both entries describe the SAME
    /// type. With the module path erased it also lets an inherent method on
    /// `inner::S` silently outrank the trait method of a DIFFERENT, top-level
    /// `S`, so the call site is answered with a contract the program never
    /// names. Measured on a program stock `rustc --edition 2021` compiles and
    /// runs (`inner::S::v() == 1`, top-level `S::v() == 2` via `impl Tr for S`):
    /// `assert!(s.v() == 1)` VERIFIED and `assert!(s.v() == 2)` was refuted —
    /// the false claim proved and the true claim rejected, simultaneously.
    ///
    /// Dropping the colliding entry is NOT the remedy: with competing
    /// declarations present, dropping the one the program named promotes the one
    /// it did not (20e12591 / 63e3bcf3). The file simply has no faithful
    /// bare-name representation, so it is rejected — order-independently, since
    /// the strike depends on the SET of declarations and not on which is written
    /// first.
    ///
    /// Unconditional over every module-level type item, annotated or not: an
    /// unannotated declaration still occupies the bare name in every one of
    /// these registries.
    pub(crate) fn reject_duplicate_type_names(&self) -> TrustVcResult<()> {
        let mut seen: BTreeMap<&str, &Vec<String>> = BTreeMap::new();
        for (module, name) in &self.types {
            if let Some(previous) = seen.insert(name.as_str(), module) {
                return Err(TrustVcError::Encoding {
                    context: RESOLUTION_CONTEXT,
                    detail: format!(
                        "two types in this file are both named `{name}` ({} and {}); method \
                         resolution is keyed by the receiver type's bare name, so the two \
                         declarations are indistinguishable and neither can be verified — \
                         rename one",
                        render_module(previous),
                        render_module(module),
                    ),
                });
            }
        }
        Ok(())
    }

    /// Resolves the trait path of an `impl <path> for T` header written inside
    /// module `scope` (empty for the file root).
    pub(crate) fn resolve_impl_trait_path(
        &self,
        scope: &[String],
        trait_path: &syn::Path,
    ) -> TraitPathResolution {
        match self.resolve_trait_path_decl(scope, trait_path) {
            Some((_, name)) => TraitPathResolution::Declared(name),
            None => self.foreign_or_undecidable(trait_path),
        }
    }

    /// As [`Self::resolve_impl_trait_path`], but answers with the DECLARATION's
    /// `(module path, ident)` rather than the ident alone. The module is what
    /// tells two same-named declarations apart, so
    /// [`prune_shadowed_duplicate_traits`] needs it; every other caller only
    /// needs the ident, because after that pass a bare ident is unique again.
    ///
    /// Not impl-specific: a trait BOUND, a SUPERTRAIT, a `dyn`/`impl Trait`
    /// position and a `where` predicate all write the same kind of path, and all
    /// of them must resolve the same way — see
    /// [`collect_trait_bound_references`].
    pub(crate) fn resolve_trait_path_decl(
        &self,
        scope: &[String],
        trait_path: &syn::Path,
    ) -> Option<(Vec<String>, String)> {
        if trait_path.leading_colon.is_some() {
            // `::krate::Tr` is unambiguously an external crate.
            return None;
        }
        let segments: Vec<String> = trait_path
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect();
        self.resolve_segments(scope, &segments, 0)
    }

    /// `path` with its head expanded through the `use` bindings visible in
    /// `scope`, following `pub use` re-export chains — the path AS WRITTEN at the
    /// import's far end, whether or not it names anything declared in this file.
    ///
    /// [`Self::resolve_trait_path_decl`] deliberately answers `None` for a trait
    /// this file does not declare, which is right for every caller that looks a
    /// DECLARATION up. It is wrong for the callers that must recognise a specific
    /// FOREIGN trait by name — `impl PartialEq for T` gates structural `==`
    /// lowering, and `use core::cmp::PartialEq as Eq2; impl Eq2 for P` defeated a
    /// last-segment test, so a hand-written non-structural `eq` went uncollected
    /// and `x == x` VERIFIED against an `eq` that always returns `false`
    /// (measured; stock `rustc --edition 2021` compiles it and prints
    /// `x == x is false`). This answers `["core", "cmp", "PartialEq"]` for that
    /// header, so the name test succeeds however the import is spelled.
    ///
    /// Expansion only ever REPLACES a head with what the program imported, so it
    /// cannot invent a name: an unbound head, a conflicting binding or an
    /// over-long chain returns the path unchanged.
    pub(crate) fn expanded_path_segments(&self, scope: &[String], path: &syn::Path) -> Vec<String> {
        let mut segments: Vec<String> = path
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect();
        if path.leading_colon.is_some() {
            return segments; // `::krate::Tr` consults no `use` binding
        }
        let mut base = scope.to_vec();
        for _ in 0..MAX_USE_CHAIN_DEPTH {
            let Some(head) = segments.first().cloned() else {
                return segments;
            };
            if matches!(head.as_str(), "crate" | "self" | "super") {
                return segments;
            }
            let key = (base.clone(), head.clone());
            if self.conflicting_use_bindings.contains(&key) {
                return segments;
            }
            if let Some(target) = self.use_bindings.get(&key) {
                let mut next = target.clone();
                next.extend_from_slice(&segments[1..]);
                segments = next;
                continue; // the target is itself written in `base`'s scope
            }
            // Not a bound head. The WALKED module may re-export the final
            // segment instead (`mod mid { pub use core::cmp::PartialEq as P; }`
            // reached as `mid::P`).
            if segments.len() > 1 {
                let (prefix, tail) = segments.split_at(segments.len() - 1);
                let mut module = base.clone();
                module.extend_from_slice(prefix);
                let tail_key = (module.clone(), tail[0].clone());
                if !self.conflicting_use_bindings.contains(&tail_key) {
                    if let Some(target) = self.use_bindings.get(&tail_key) {
                        segments = target.clone();
                        base = module;
                        continue;
                    }
                }
            }
            return segments;
        }
        segments
    }

    /// Bare idents declared by MORE THAN ONE `trait` item in this file.
    ///
    /// Exactly the set [`Self::reject_duplicate_trait_names`] strikes on, and
    /// exactly the set [`prune_shadowed_duplicate_traits`] must decide before
    /// that gate runs.
    pub(crate) fn duplicate_trait_idents(&self) -> BTreeSet<String> {
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        let mut duplicated = BTreeSet::new();
        for (_, name) in &self.traits {
            if !seen.insert(name.as_str()) {
                duplicated.insert(name.clone());
            }
        }
        duplicated
    }

    /// The outcome for a path that named no in-file trait: `Foreign` only when
    /// the last segment cannot be mistaken for an in-file declaration.
    fn foreign_or_undecidable(&self, trait_path: &syn::Path) -> TraitPathResolution {
        let Some(last) = trait_path.segments.last().map(|s| s.ident.to_string()) else {
            return TraitPathResolution::Undecidable(
                "trait path has no segments to resolve".to_string(),
            );
        };
        if self.trait_idents.contains(&last) {
            // This is the exact step the old code took unconditionally, and the
            // one that answered with a declaration the program does not name.
            return TraitPathResolution::Undecidable(format!(
                "`{}` does not resolve to a trait declared in this file, but a different trait \
                 named `{last}` is declared here; resolving it by bare name would attribute the \
                 wrong trait's contract",
                render_path(trait_path),
            ));
        }
        TraitPathResolution::Foreign(last)
    }

    /// Resolves `segments` (written in module `scope`) to an in-file trait
    /// declaration's `(module path, ident)`, or `None` when no in-file trait is
    /// named.
    fn resolve_segments(
        &self,
        scope: &[String],
        segments: &[String],
        depth: usize,
    ) -> Option<(Vec<String>, String)> {
        if depth > MAX_USE_CHAIN_DEPTH || segments.is_empty() {
            return None;
        }
        let (base, rest, qualified) = match segments[0].as_str() {
            "crate" => (Vec::new(), &segments[1..], true),
            "self" => (scope.to_vec(), &segments[1..], true),
            "super" => {
                let mut base = scope.to_vec();
                let mut consumed = 0;
                while consumed < segments.len() && segments[consumed] == "super" {
                    base.pop()?;
                    consumed += 1;
                }
                (base, &segments[consumed..], true)
            }
            _ => (scope.to_vec(), segments, false),
        };
        if rest.is_empty() {
            return None;
        }

        // An UNQUALIFIED head may be a name a `use` bound into this module —
        // including a rename, which is the whole point. A qualified path
        // (`crate::`/`self::`/`super::`) never consults `use` bindings.
        if !qualified {
            let key = (base.clone(), rest[0].clone());
            if self.conflicting_use_bindings.contains(&key) {
                return None;
            }
            if let Some(target) = self.use_bindings.get(&key) {
                // The head is ALSO a module declared right here: `use a::b as m;`
                // next to `mod m { .. }` occupies the type namespace twice
                // (rustc E0255). Pick nothing.
                if rest.len() > 1 && self.inline_modules.contains(&join(&base, &rest[0])) {
                    return None;
                }
                let mut next = target.clone();
                next.extend_from_slice(&rest[1..]);
                // The `use` target path is itself written in `base`'s scope.
                let through_use = self.resolve_segments(&base, &next, depth + 1);
                // NAMESPACES. A `use` binding and a `trait` declaration may
                // legitimately share an ident in the same module when the import
                // lands in the VALUE namespace: `use helpers::make as Orig;`
                // alongside `trait Orig` compiles and runs under stock rustc
                // (measured, and it runs). This index does not track namespaces,
                // so a `use` binding that does not lead to a trait must fall
                // through to the local declaration rather than poison the path —
                // an earlier cut returned `None` here and hard-errored that legal
                // program, a capability regression against the pre-fix engine.
                //
                // When BOTH lead to a trait the program is genuinely ill-formed
                // (E0255: the type namespace really is occupied twice), so
                // nothing is picked — `None` reaches the caller's collision guard
                // and the file fails closed.
                let declared_here = rest.len() == 1 && self.traits.contains(&key);
                match (through_use, declared_here) {
                    (Some(_), true) => return None,
                    (Some(found), false) => return Some(found),
                    (None, true) => return Some((base.clone(), rest[0].clone())),
                    (None, false) => {}
                }
            }
        }

        // Walk the module prefix from `base` and look the trait up exactly.
        let (prefix, tail) = rest.split_at(rest.len() - 1);
        let name = &tail[0];
        let mut module = base.clone();
        module.extend_from_slice(prefix);
        if self.traits.contains(&(module.clone(), name.clone())) {
            return Some((module, name.clone()));
        }

        // The walked module may RE-EXPORT the name rather than declare it
        // (`mod mid { pub use crate::deep::Orig as Mid; }` reached as
        // `mid::Mid`). Follow the re-export from that module's own scope. Only
        // reached after the exact declaration lookup failed, so this can never
        // divert a path that already named a declaration.
        if let Some(target) = self.use_bindings.get(&(module.clone(), name.clone())) {
            if !self
                .conflicting_use_bindings
                .contains(&(module.clone(), name.clone()))
            {
                let target = target.clone();
                return self.resolve_segments(&module, &target, depth + 1);
            }
        }

        // A bare name may have arrived through a glob import. Resolve each glob
        // prefix to an in-file module and look there. Zero hits falls through to
        // the caller's collision guard; the duplicate-name gate guarantees at
        // most one hit can exist in the whole file.
        if rest.len() == 1 && !qualified {
            for glob_prefix in self.glob_prefixes.get(&base).into_iter().flatten() {
                let Some(glob_module) = self.resolve_module(&base, glob_prefix, depth + 1) else {
                    continue;
                };
                if self.traits.contains(&(glob_module.clone(), name.clone())) {
                    return Some((glob_module, name.clone()));
                }
            }
        }
        None
    }

    /// Resolves `segments` (written in module `scope`) to an inline module path
    /// present in this file.
    fn resolve_module(
        &self,
        scope: &[String],
        segments: &[String],
        depth: usize,
    ) -> Option<Vec<String>> {
        if depth > MAX_USE_CHAIN_DEPTH || segments.is_empty() {
            return None;
        }
        let (base, rest, qualified) = match segments[0].as_str() {
            "crate" => (Vec::new(), &segments[1..], true),
            "self" => (scope.to_vec(), &segments[1..], true),
            "super" => {
                let mut base = scope.to_vec();
                let mut consumed = 0;
                while consumed < segments.len() && segments[consumed] == "super" {
                    base.pop()?;
                    consumed += 1;
                }
                (base, &segments[consumed..], true)
            }
            _ => (scope.to_vec(), segments, false),
        };
        if rest.is_empty() {
            return Some(base);
        }
        if !qualified {
            let key = (base.clone(), rest[0].clone());
            if self.conflicting_use_bindings.contains(&key) {
                return None;
            }
            if let Some(target) = self.use_bindings.get(&key) {
                let mut next = target.clone();
                next.extend_from_slice(&rest[1..]);
                return self.resolve_module(&base, &next, depth + 1);
            }
        }
        let mut module = base;
        module.extend_from_slice(rest);
        self.inline_modules.contains(&module).then_some(module)
    }

    fn collect_items(&mut self, items: &[syn::Item], module: &mut Vec<String>) {
        for item in items {
            match item {
                syn::Item::Trait(item_trait) => {
                    self.trait_idents.insert(item_trait.ident.to_string());
                    self.traits
                        .insert((module.clone(), item_trait.ident.to_string()));
                }
                // Module-level type declarations only, exactly matching the
                // trait scope above. A type declared inside a FUNCTION body is
                // not collected here and does not need to be: nested items in a
                // verified function body are rejected outright by body
                // extraction ("Unsupported nested struct item in function
                // body"), so such a declaration can never reach the
                // bare-name-keyed method registry.
                syn::Item::Struct(item_struct) => {
                    self.types
                        .insert((module.clone(), item_struct.ident.to_string()));
                }
                syn::Item::Enum(item_enum) => {
                    self.types
                        .insert((module.clone(), item_enum.ident.to_string()));
                }
                syn::Item::Union(item_union) => {
                    self.types
                        .insert((module.clone(), item_union.ident.to_string()));
                }
                syn::Item::Use(item_use) => {
                    self.collect_use_tree(&item_use.tree, module, &mut Vec::new());
                }
                syn::Item::Mod(item_mod) => {
                    // An out-of-line `mod m;` contributes no declarations here.
                    // It is deliberately NOT recorded as an inline module: a
                    // path through it resolves to no in-file trait, and the
                    // caller's collision guard then decides between `Foreign`
                    // and `Undecidable`.
                    if let Some((_, inner)) = &item_mod.content {
                        module.push(item_mod.ident.to_string());
                        self.inline_modules.insert(module.clone());
                        self.collect_items(inner, module);
                        module.pop();
                    }
                }
                _ => {}
            }
        }
    }

    fn collect_use_tree(
        &mut self,
        tree: &syn::UseTree,
        module: &[String],
        prefix: &mut Vec<String>,
    ) {
        match tree {
            syn::UseTree::Path(path) => {
                prefix.push(path.ident.to_string());
                self.collect_use_tree(&path.tree, module, prefix);
                prefix.pop();
            }
            syn::UseTree::Name(name) => {
                let mut target = prefix.clone();
                target.push(name.ident.to_string());
                self.bind_use(module, name.ident.to_string(), target);
            }
            syn::UseTree::Rename(rename) => {
                let mut target = prefix.clone();
                target.push(rename.ident.to_string());
                self.bind_use(module, rename.rename.to_string(), target);
            }
            syn::UseTree::Glob(_) => {
                self.glob_prefixes
                    .entry(module.to_vec())
                    .or_default()
                    .push(prefix.clone());
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    self.collect_use_tree(item, module, prefix);
                }
            }
        }
    }

    fn bind_use(&mut self, module: &[String], local: String, target: Vec<String>) {
        let key = (module.to_vec(), local);
        match self.use_bindings.entry(key.clone()) {
            std::collections::btree_map::Entry::Occupied(existing) => {
                if existing.get() != &target {
                    self.conflicting_use_bindings.insert(key);
                }
            }
            std::collections::btree_map::Entry::Vacant(slot) => {
                slot.insert(target);
            }
        }
    }
}

fn join(module: &[String], name: &str) -> Vec<String> {
    let mut path = module.to_vec();
    path.push(name.to_string());
    path
}

fn render_module(module: &[String]) -> String {
    if module.is_empty() {
        "the file root".to_string()
    } else {
        format!("`{}`", module.join("::"))
    }
}

fn render_path(path: &syn::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>()
        .join("::")
}

/// Deletes every `trait` declaration whose bare ident is duplicated in `file`
/// and which NOTHING in the file names, or fails the file closed when that
/// cannot be decided.
///
/// Returns `Ok(None)` — and touches nothing — for the overwhelmingly common file
/// whose trait idents are already unique.
///
/// # Why a prune and not a narrowed gate
///
/// [`TraitScopeIndex::reject_duplicate_trait_names`] is unconditional and must
/// stay that way: trait BOUNDS (`fn g<T: Tr>`), SUPERTRAITS,
/// `register_trait_decl_self_receiver_kinds`, `trait_method_declares_requires`
/// and the parameterized-trait shape probes in `vc_extraction` all key on a
/// path's LAST SEGMENT with no scope resolution whatsoever. They cannot answer
/// with the WRONG trait only because that gate guarantees a bare ident denotes
/// at most one in-file trait. Narrowing the gate would silently reopen every one
/// of those lanes.
///
/// So the guarantee is RESTORED instead of waived. `impl real::Tr for S` is not
/// ambiguous — the qualifier names exactly one declaration — and once the
/// declarations nothing names are gone, the file the gate sees genuinely has
/// unique trait idents and every consumer above is correct by construction.
///
/// # Every naming site votes, and they must AGREE
///
/// A trait is not named only by `impl` headers. `fn g<T: real::Tr>`,
/// `trait Sub: real::Tr`, `&dyn real::Tr`, `impl real::Tr` and
/// `where T: real::Tr` all name a declaration too, and all of them are recorded
/// downstream by the path's LAST SEGMENT. An earlier cut therefore rejected any
/// file where a duplicated ident reached a bound. That rejection was load-bearing
/// and this is what it was protecting against, MEASURED through the production
/// CLI with the sweep neutered:
///
/// ```text
/// mod decoy { trait Tr { ensures(result == 9) fn m(&self) -> u64; } }
/// mod real  { trait Tr { ensures(result == 7) fn m(&self) -> u64; } }
/// impl decoy::Tr for D { .. }                 // the only impl: decoy survives
/// fn g_pos<T: real::Tr>(x: T)  { assert!(x.m() == 7u64); }   // TRUE  -> unknown
/// fn g_liar<T: real::Tr>(x: T) { assert!(x.m() == 9u64); }   // FALSE -> VERIFIED
/// ```
///
/// The false claim proved and the true claim rejected, simultaneously — this
/// class's signature — because the bound's `"Tr"` was answered by the survivor
/// the IMPL had chosen. So the remedy is not to reject the bound but to let it
/// VOTE: every bound path is resolved through the same scope index the impl
/// headers use, and its declaration is recorded as a reference. A duplicated
/// ident survives only when every site that names it — impls and bounds alike —
/// resolves to ONE declaration; the file then genuinely has unique trait idents
/// and the last segment is faithful again. The program above now fails closed on
/// the disagreement instead of answering with the wrong trait.
///
/// # What is still rejected, and why each one has to be
///
/// * A bound, supertrait, `dyn`/`impl Trait` position or `where` predicate whose
///   last segment is a duplicated ident but which resolves to NO in-file
///   declaration (`T: absent::Tr`, or a bare `T: Tr` with two candidates and no
///   disambiguating `use`). The last segment would still key to the survivor,
///   which is the coin flip above.
/// * An impl header in the same shape — a bare `impl Tr for S` with two
///   candidates. (Stock rustc rejects that program too: E0405.)
/// * Two naming sites resolving to two DIFFERENT declarations of one ident. Both
///   are live, so no prune can make the bare-name key faithful.
/// * A duplicated ident nothing in the file names at all: nothing selects a
///   survivor, so there is nothing to prune to.
///
/// A bound that resolves through a RENAME (`use decoy::Tr as Other;`,
/// `T: Other`) votes for `decoy::Tr` like any other reference, and is then inert
/// downstream — `append_trait_bounds` records `"Other"`, which names no
/// declaration — exactly as a renamed bound already behaves in a file with no
/// duplicates at all.
pub(crate) fn prune_shadowed_duplicate_traits(
    file: &syn::File,
) -> TrustVcResult<Option<syn::File>> {
    let index = TraitScopeIndex::build(file);
    let duplicated = index.duplicate_trait_idents();
    if duplicated.is_empty() {
        return Ok(None);
    }

    let mut referenced: BTreeMap<String, BTreeSet<Vec<String>>> = BTreeMap::new();
    let mut unresolved: Option<String> = None;
    collect_impl_trait_references(
        &index,
        &file.items,
        &mut Vec::new(),
        &duplicated,
        &mut referenced,
        &mut unresolved,
    );
    if let Some(path) = unresolved {
        return Err(TrustVcError::Encoding {
            context: RESOLUTION_CONTEXT,
            detail: format!(
                "`impl {path} for ..` names no trait declared in this file, but `{path}` is the \
                 bare name of two different traits declared here; resolving it by bare name would \
                 attribute the wrong trait's contract — qualify the impl header with the module \
                 that declares the trait, or rename one",
            ),
        });
    }

    if let Some(path) = collect_trait_bound_references(&index, file, &duplicated, &mut referenced) {
        return Err(TrustVcError::Encoding {
            context: RESOLUTION_CONTEXT,
            detail: format!(
                "the trait bound `{path}` names no trait declared in this file, but `{path}` is \
                 the bare name of two different traits declared here; bounds and supertraits are \
                 recorded by the path's last segment alone, so resolving it that way would \
                 attribute the wrong trait's contract — qualify the bound with the module that \
                 declares the trait, or rename one",
            ),
        });
    }

    let mut survivors: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for name in &duplicated {
        let mut modules = referenced
            .get(name)
            .cloned()
            .unwrap_or_default()
            .into_iter();
        match (modules.next(), modules.next()) {
            (Some(module), None) => {
                survivors.insert(name.clone(), module);
            }
            (Some(first), Some(second)) => {
                return Err(TrustVcError::Encoding {
                    context: RESOLUTION_CONTEXT,
                    detail: format!(
                        "two traits in this file are both named `{name}` ({} and {}) and this \
                         file names BOTH (in an `impl` header, a trait bound or a supertrait); \
                         trait registration is keyed by the trait's bare name, so the two \
                         declarations are indistinguishable and neither can be verified — \
                         rename one",
                        render_module(&first),
                        render_module(&second),
                    ),
                });
            }
            (None, _) => {
                return Err(TrustVcError::Encoding {
                    context: RESOLUTION_CONTEXT,
                    detail: format!(
                        "two traits in this file are both named `{name}` and nothing in this file \
                         names either of them — no `impl` header, no trait bound, no supertrait; \
                         trait registration is keyed by the trait's bare name, so the two \
                         declarations are indistinguishable and neither can be verified — \
                         rename one",
                    ),
                });
            }
        }
    }

    let mut pruned = file.clone();
    retain_surviving_traits(&mut pruned.items, &mut Vec::new(), &survivors);
    // POST-CONDITION, not decoration: everything downstream is allowed to key by
    // bare ident ONLY because this holds. If a prune ever left two same-named
    // declarations standing, the file must fail closed exactly as before.
    TraitScopeIndex::build(&pruned).reject_duplicate_trait_names()?;
    Ok(Some(pruned))
}

/// Resolves every trait BOUND in `file` and records, per duplicated ident, the
/// DECLARATION module it names — the bound's vote in the survivor election.
///
/// Returns the first bound path that names no in-file declaration while its last
/// segment IS a duplicated ident. That one cannot vote and cannot be pruned
/// around: `append_trait_bounds` would key it to whichever declaration survived.
/// The caller must fail the file closed on it.
///
/// Deliberately a whole-file sweep rather than a hand-rolled walk of function
/// signatures: `syn::TraitBound` is also how supertrait lists, `dyn Tr`,
/// `impl Tr`, `where` predicates and associated-type bounds are spelled, and
/// every one of those reaches a last-segment-keyed consumer. An
/// `impl <path> for T` header is NOT a `TraitBound` (it is a bare `syn::Path`),
/// so impl headers are correctly excluded here — `collect_impl_trait_references`
/// already votes for them, and double-counting them would be harmless but
/// redundant.
///
/// The MODULE a bound is written in decides how its path resolves, so the sweep
/// tracks the inline-module path rather than resolving everything from the file
/// root; `mod real { trait Sub: Tr {} }` names `real::Tr`, not a root `Tr`.
/// A `mod` nested in a function BODY pushes its ident too: that can only make a
/// path fail to resolve (such items are not indexed as declarations at all), and
/// a failure to resolve is the fail-closed direction.
fn collect_trait_bound_references(
    index: &TraitScopeIndex,
    file: &syn::File,
    duplicated: &BTreeSet<String>,
    referenced: &mut BTreeMap<String, BTreeSet<Vec<String>>>,
) -> Option<String> {
    struct BoundScan<'a> {
        index: &'a TraitScopeIndex,
        duplicated: &'a BTreeSet<String>,
        module: Vec<String>,
        referenced: &'a mut BTreeMap<String, BTreeSet<Vec<String>>>,
        unresolved: Option<String>,
    }
    impl BoundScan<'_> {
        fn record(&mut self, path: &syn::Path) {
            match self.index.resolve_trait_path_decl(&self.module, path) {
                // The RESOLVED ident is what is recorded, never the written one:
                // under `use decoy::Tr as Other; fn g<T: Other>` the last segment
                // is not even a duplicate, yet the bound names one of the two
                // `Tr`s and must keep it alive.
                Some((module, name)) => {
                    if self.duplicated.contains(&name) {
                        self.referenced.entry(name).or_default().insert(module);
                    }
                }
                // A path naming no in-file trait is only harmless when its last
                // segment cannot be mistaken for one of the duplicates — the
                // same rule `foreign_or_undecidable` applies to impl headers.
                // `T: Clone` in a file that duplicates `Tr` is untouched.
                None => {
                    let names_a_duplicate = path
                        .segments
                        .last()
                        .is_some_and(|segment| duplicated_contains(self.duplicated, segment));
                    if names_a_duplicate && self.unresolved.is_none() {
                        self.unresolved = Some(render_path(path));
                    }
                }
            }
        }
    }
    fn duplicated_contains(duplicated: &BTreeSet<String>, segment: &syn::PathSegment) -> bool {
        duplicated.contains(&segment.ident.to_string())
    }
    impl<'ast> syn::visit::Visit<'ast> for BoundScan<'_> {
        fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
            if item.content.is_some() {
                self.module.push(item.ident.to_string());
                syn::visit::visit_item_mod(self, item);
                self.module.pop();
            } else {
                syn::visit::visit_item_mod(self, item);
            }
        }
        fn visit_trait_bound(&mut self, bound: &'ast syn::TraitBound) {
            self.record(&bound.path);
            syn::visit::visit_trait_bound(self, bound);
        }
    }
    let mut scan = BoundScan {
        index,
        duplicated,
        module: Vec::new(),
        referenced,
        unresolved: None,
    };
    syn::visit::Visit::visit_file(&mut scan, file);
    scan.unresolved
}

/// Records, per duplicated ident, the DECLARATION modules the file's `impl`
/// headers resolve to.
///
/// Unannotated impls count too — `#[trust_vc::trait_impl]` gates the conformance
/// lane, but the receiver-kind registry and the trait-shape probes read every
/// `impl <Trait> for T` block in the file, so an unannotated impl keeps its
/// declaration live just as much.
///
/// The RESOLVED ident is what is recorded, never the written one: under
/// `use decoy::Tr as Other; impl Other for S` the last segment is `Other`, which
/// is not duplicated, yet the impl still names one of the two `Tr`s.
fn collect_impl_trait_references(
    index: &TraitScopeIndex,
    items: &[syn::Item],
    module: &mut Vec<String>,
    duplicated: &BTreeSet<String>,
    referenced: &mut BTreeMap<String, BTreeSet<Vec<String>>>,
    unresolved: &mut Option<String>,
) {
    for item in items {
        match item {
            syn::Item::Impl(item_impl) => {
                let Some((_, trait_path, _)) = &item_impl.trait_ else {
                    continue;
                };
                match index.resolve_trait_path_decl(module, trait_path) {
                    Some((declaring_module, name)) => {
                        if duplicated.contains(&name) {
                            referenced.entry(name).or_default().insert(declaring_module);
                        }
                    }
                    None => {
                        // Unresolvable AND colliding: this is the shape whose old
                        // last-segment key answered with a declaration the program
                        // does not name.
                        let last = trait_path
                            .segments
                            .last()
                            .map(|segment| segment.ident.to_string());
                        if let Some(last) = last {
                            if duplicated.contains(&last) && unresolved.is_none() {
                                *unresolved = Some(last);
                            }
                        }
                    }
                }
            }
            syn::Item::Mod(item_mod) => {
                if let Some((_, inner)) = &item_mod.content {
                    module.push(item_mod.ident.to_string());
                    collect_impl_trait_references(
                        index, inner, module, duplicated, referenced, unresolved,
                    );
                    module.pop();
                }
            }
            _ => {}
        }
    }
}

/// Drops each `trait` item whose ident is duplicated and whose module is not the
/// surviving declaration's.
fn retain_surviving_traits(
    items: &mut Vec<syn::Item>,
    module: &mut Vec<String>,
    survivors: &BTreeMap<String, Vec<String>>,
) {
    items.retain(|item| match item {
        syn::Item::Trait(item_trait) => {
            match survivors.get(&item_trait.ident.to_string()) {
                Some(surviving_module) => surviving_module.as_slice() == module.as_slice(),
                // Not a duplicated ident: keep.
                None => true,
            }
        }
        _ => true,
    });
    for item in items.iter_mut() {
        if let syn::Item::Mod(item_mod) = item {
            if let Some((_, inner)) = &mut item_mod.content {
                module.push(item_mod.ident.to_string());
                retain_surviving_traits(inner, module, survivors);
                module.pop();
            }
        }
    }
}

/// Resolves an `impl <Trait> for <Type>` header's trait name, or fails the file
/// closed. `scope` is the module path the impl is written in.
pub(crate) fn resolved_impl_trait_name(
    index: &TraitScopeIndex,
    scope: &[String],
    item_impl: &syn::ItemImpl,
) -> TrustVcResult<Option<String>> {
    let Some((_, trait_path, _)) = &item_impl.trait_ else {
        return Ok(None);
    };
    match index.resolve_impl_trait_path(scope, trait_path) {
        TraitPathResolution::Declared(name) | TraitPathResolution::Foreign(name) => Ok(Some(name)),
        TraitPathResolution::Undecidable(reason) => Err(TrustVcError::Encoding {
            context: RESOLUTION_CONTEXT,
            detail: reason,
        }),
    }
}

/// The DECLARATION idents named by `item_trait`'s supertrait bounds
/// (`trait Derived: Base`), written in module `scope`.
///
/// Mirrors `trait_expand::parse_trait_decl`'s filtering — plain `Trait` bounds
/// with the default modifier only, deduplicated, order preserved — and replaces
/// its last-segment keying.
///
/// SOUNDNESS (rename), a MEASURED CARDINAL. `TraitDecl::supertraits` is walked by
/// `supertrait_closure_methods` to decide which trait declares an inherited
/// method and which contract answers a call through the derived bound. Keying it
/// by the supertrait path's last segment answers a renamed supertrait with
/// whatever declaration happens to bear that spelling:
///
/// ```text
/// mod origin { trait Base { ensures(result == 7) fn b(&self) -> u64; } }
/// mod other  { trait Peek { ensures(result == 9) fn b(&self) -> u64; } }
/// use origin::Base as Peek;
/// trait Derived: Peek { fn d(&self) -> u64; }
/// fn probe<T: Derived>(x: T) { assert!(x.b() == 9u64); }   // FALSE — truth is 7
/// ```
///
/// The FALSE claim **verified** and its TRUE twin (`== 7u64`) was refuted, on a
/// program stock `rustc --edition 2021` compiles and runs (it prints
/// `probe(S) = 7`). Every declaration ident is distinct, so the duplicate-ident
/// gate and the supertrait VOTE in [`prune_shadowed_duplicate_traits`] — which
/// engage only on a duplicated ident — never see it. The plain rename
/// (`trait Derived: Alias` naming nothing) was the fail-closed half of the same
/// defect and cost the whole supertrait-inheritance capability.
///
/// An UNDECIDABLE bound records NO supertrait, for the reason
/// `resolved_trait_bounds_from_signature` gives: keeping the last segment IS the
/// wrong-trait step, and a supertrait is a lookup key, not a declaration — every
/// declaration stays registered, so an unambiguous sibling site still resolves,
/// while the omitted edge leaves the inherited method unsupported (fail-closed).
pub(crate) fn resolved_supertrait_names(
    index: &TraitScopeIndex,
    scope: &[String],
    item_trait: &syn::ItemTrait,
) -> Vec<String> {
    let mut names = Vec::new();
    for bound in &item_trait.supertraits {
        let syn::TypeParamBound::Trait(trait_bound) = bound else {
            continue;
        };
        if !matches!(trait_bound.modifier, syn::TraitBoundModifier::None) {
            continue;
        }
        let name = match index.resolve_impl_trait_path(scope, &trait_bound.path) {
            TraitPathResolution::Declared(name) | TraitPathResolution::Foreign(name) => name,
            TraitPathResolution::Undecidable(_) => continue,
        };
        if !names.contains(&name) {
            names.push(name);
        }
    }
    names
}

#[cfg(test)]
mod tests {
    use super::*;

    fn index(src: &str) -> TraitScopeIndex {
        TraitScopeIndex::build(&syn::parse_file(src).expect("parse"))
    }

    fn first_impl(src: &str) -> syn::ItemImpl {
        fn find(items: &[syn::Item]) -> Option<syn::ItemImpl> {
            for item in items {
                match item {
                    syn::Item::Impl(item_impl) if item_impl.trait_.is_some() => {
                        return Some(item_impl.clone())
                    }
                    syn::Item::Mod(m) => {
                        if let Some((_, inner)) = &m.content {
                            if let Some(found) = find(inner) {
                                return Some(found);
                            }
                        }
                    }
                    _ => {}
                }
            }
            None
        }
        find(&syn::parse_file(src).expect("parse").items).expect("a trait impl")
    }

    fn resolve(src: &str, scope: &[&str]) -> TraitPathResolution {
        let scope: Vec<String> = scope.iter().map(|s| (*s).to_string()).collect();
        let item_impl = first_impl(src);
        let (_, path, _) = item_impl.trait_.as_ref().unwrap();
        index(src).resolve_impl_trait_path(&scope, path)
    }

    #[test]
    fn unaliased_impl_still_resolves_to_the_declaration() {
        let src = "mod inner { pub trait Orig {} } use inner::Orig; struct T; impl Orig for T {}";
        assert_eq!(
            resolve(src, &[]),
            TraitPathResolution::Declared("Orig".to_string())
        );
    }

    #[test]
    fn use_rename_resolves_to_the_declarations_name() {
        let src = "mod inner { pub trait Orig {} } use inner::Orig as Alias; struct T; \
                   impl Alias for T {}";
        assert_eq!(
            resolve(src, &[]),
            TraitPathResolution::Declared("Orig".to_string())
        );
    }

    #[test]
    fn a_rename_wins_over_a_same_named_trait_in_another_module() {
        // The exact cardinal shape: `Alias` also names a trait in `decoy`, which
        // is NOT in scope at the file root. The rename must win.
        let src = "mod decoy { pub trait Alias {} } mod origin { pub trait Orig {} } \
                   use origin::Orig as Alias; struct S; impl Alias for S {}";
        assert_eq!(
            resolve(src, &[]),
            TraitPathResolution::Declared("Orig".to_string())
        );
    }

    /// The shape that VERIFIED a false claim and REFUTED the true one: an
    /// inherent `v` on `inner::S` outranked the trait `v` of a different,
    /// top-level `S`, because all method metadata is keyed by the bare ident.
    #[test]
    fn two_types_sharing_a_bare_ident_are_rejected() {
        let src = "mod inner { pub struct S; impl S { pub fn v(&self) -> u8 { 1 } } } \
                   pub struct S; trait Tr { fn v(&self) -> u8; } \
                   impl Tr for S { fn v(&self) -> u8 { 2 } }";
        let err = index(src)
            .reject_duplicate_type_names()
            .expect_err("two types named `S` must fail the file closed");
        let rendered = format!("{err}");
        assert!(rendered.contains('S'), "{rendered}");
        assert!(rendered.contains("bare name"), "{rendered}");
    }

    /// Order-independence: the strike depends on the SET of declarations, not on
    /// which one the file writes first. Both orders must fail closed, or the
    /// gate would merely relocate the first-declaration-wins bug.
    #[test]
    fn duplicate_type_rejection_is_order_independent() {
        let forward = "mod inner { pub struct S; } pub struct S;";
        let reverse = "pub struct S; mod inner { pub struct S; }";
        assert!(index(forward).reject_duplicate_type_names().is_err());
        assert!(index(reverse).reject_duplicate_type_names().is_err());
    }

    /// Every type item namespace occupies the bare name, annotated or not.
    #[test]
    fn duplicate_type_rejection_spans_struct_and_enum_kinds() {
        let src = "mod inner { pub enum S { A } } pub struct S;";
        assert!(index(src).reject_duplicate_type_names().is_err());
    }

    /// NARROWNESS. Distinct idents in distinct modules stay legal — this is the
    /// pin that keeps the gate from becoming a blanket rejection of modules.
    #[test]
    fn distinct_type_names_are_accepted() {
        let src = "mod inner { pub struct S; impl S { pub fn v(&self) -> u8 { 1 } } } \
                   pub struct Other; impl Other { pub fn v(&self) -> u8 { 2 } }";
        assert!(index(src).reject_duplicate_type_names().is_ok());
    }

    /// NARROWNESS. A type declared inside a FUNCTION body is not collected: two
    /// sibling functions may each declare their own local `S` (the corpus does
    /// exactly this in `evals/verus/ported/recursive_types.rs`), and body
    /// extraction already rejects nested items outright, so such a declaration
    /// can never reach the bare-name method registry.
    #[test]
    fn function_local_types_do_not_collide() {
        let src = "fn f() { struct S; } fn g() { struct S; }";
        assert!(index(src).reject_duplicate_type_names().is_ok());
    }

    /// NARROWNESS. A type and a TRAIT may share an ident — they live in
    /// different namespaces and the two gates are independent.
    #[test]
    fn a_type_and_a_trait_may_share_an_ident() {
        let src = "pub struct S; pub trait S2 {} mod m { pub trait S {} }";
        assert!(index(src).reject_duplicate_type_names().is_ok());
        assert!(index(src).reject_duplicate_trait_names().is_ok());
    }

    #[test]
    fn a_reexport_chain_is_followed() {
        let src = "mod deep { pub trait Orig {} } \
                   mod mid { pub use crate::deep::Orig as Mid; } \
                   use mid::Mid as Outer; struct T; impl Outer for T {}";
        assert_eq!(
            resolve(src, &[]),
            TraitPathResolution::Declared("Orig".to_string())
        );
    }

    #[test]
    fn a_nested_module_path_resolves() {
        let src = "mod a { pub mod b { pub trait Deep {} } } struct T; impl a::b::Deep for T {}";
        assert_eq!(
            resolve(src, &[]),
            TraitPathResolution::Declared("Deep".to_string())
        );
    }

    #[test]
    fn a_crate_qualified_path_resolves_from_inside_a_module() {
        let src = "mod c { pub trait Tr {} } \
                   mod i { pub struct T; impl crate::c::Tr for T {} }";
        assert_eq!(
            resolve(src, &["i"]),
            TraitPathResolution::Declared("Tr".to_string())
        );
    }

    #[test]
    fn a_super_qualified_path_resolves() {
        let src = "mod c { pub trait Tr {} } \
                   mod i { pub struct T; impl super::c::Tr for T {} }";
        assert_eq!(
            resolve(src, &["i"]),
            TraitPathResolution::Declared("Tr".to_string())
        );
    }

    #[test]
    fn a_glob_import_resolves_to_the_single_in_file_declaration() {
        let src = "mod inner { pub trait Orig {} } use inner::*; struct T; impl Orig for T {}";
        assert_eq!(
            resolve(src, &[]),
            TraitPathResolution::Declared("Orig".to_string())
        );
    }

    #[test]
    fn a_foreign_trait_keeps_its_last_segment() {
        let src = "struct T; impl core::fmt::Debug for T {}";
        assert_eq!(
            resolve(src, &[]),
            TraitPathResolution::Foreign("Debug".to_string())
        );
    }

    #[test]
    fn an_unresolvable_path_whose_last_segment_collides_is_undecidable() {
        // `far::Tr` names nothing in this file, but `a::Tr` is declared here.
        // Keying by the last segment would hand `a::Tr`'s contract to this impl.
        let src = "mod a { pub trait Tr {} } struct T; impl far::Tr for T {}";
        assert!(matches!(
            resolve(src, &[]),
            TraitPathResolution::Undecidable(_)
        ));
    }

    #[test]
    fn an_out_of_line_module_path_is_undecidable_when_the_name_collides() {
        let src = "mod m; mod a { pub trait Tr {} } struct T; impl m::Tr for T {}";
        assert!(matches!(
            resolve(src, &[]),
            TraitPathResolution::Undecidable(_)
        ));
    }

    #[test]
    fn duplicate_trait_names_fail_the_file_closed() {
        let src = "mod a { pub trait Tr {} } mod b { pub trait Tr {} }";
        assert!(index(src).reject_duplicate_trait_names().is_err());
    }

    #[test]
    fn distinct_trait_names_pass_the_duplicate_gate() {
        let src = "mod a { pub trait Tr {} } mod b { pub trait Other {} } trait Third {}";
        assert!(index(src).reject_duplicate_trait_names().is_ok());
    }

    #[test]
    fn an_aliased_type_or_fn_import_does_not_disturb_trait_resolution() {
        let src = "mod inner { pub trait Orig {} pub struct Thing; pub fn helper() {} } \
                   use inner::{Orig, Thing as Renamed, helper as h}; \
                   struct T; impl Orig for T {}";
        assert_eq!(
            resolve(src, &[]),
            TraitPathResolution::Declared("Orig".to_string())
        );
    }

    #[test]
    fn a_value_namespace_import_sharing_a_traits_ident_does_not_poison_it() {
        // `use helpers::make as Orig;` binds the VALUE namespace; `trait Orig`
        // binds the type namespace. Stock rustc compiles and runs this. The
        // `use` must not shadow the declaration in a trait position.
        let src = "mod helpers { pub fn make() -> u64 { 1 } } \
                   use helpers::make as Orig; \
                   pub trait Orig { fn m(&self) -> u64; } \
                   struct T; impl Orig for T { fn m(&self) -> u64 { 7 } }";
        assert_eq!(
            resolve(src, &[]),
            TraitPathResolution::Declared("Orig".to_string())
        );
    }

    #[test]
    fn a_use_and_a_trait_that_both_name_traits_pick_nothing() {
        // Both sides land in the type namespace — rustc E0255. Nothing is picked.
        let src = "mod inner { pub trait Other {} } \
                   use inner::Other as Orig; \
                   pub trait Orig {} \
                   struct T; impl Orig for T {}";
        assert!(matches!(
            resolve(src, &[]),
            TraitPathResolution::Undecidable(_)
        ));
    }

    #[test]
    fn a_cyclic_use_chain_terminates_undecidable() {
        let src = "mod a { pub trait Zed {} } use self::b::Loop as Loop2; \
                   mod b { pub use crate::Loop2 as Loop; } struct T; impl Loop2 for T {}";
        // Whatever it decides, it must terminate and must not invent `Zed`.
        assert!(!matches!(
            resolve(src, &[]),
            TraitPathResolution::Declared(ref n) if n == "Zed"
        ));
    }

    // -----------------------------------------------------------------------
    // `prune_shadowed_duplicate_traits`: the duplicate-name gate must not cost
    // legal programs, and must not stop protecting the last-segment-keyed lanes.
    // -----------------------------------------------------------------------

    fn prune(src: &str) -> TrustVcResult<Option<syn::File>> {
        prune_shadowed_duplicate_traits(&syn::parse_file(src).expect("parse"))
    }

    /// The surviving declaration's module path for `ident`, or `None` when the
    /// file no longer declares it.
    fn surviving_module(file: &syn::File, ident: &str) -> Option<Vec<String>> {
        TraitScopeIndex::build(file)
            .traits
            .iter()
            .find(|(_, name)| name == ident)
            .map(|(module, _)| module.clone())
    }

    /// NARROWNESS, and the hot path: a file with unique trait idents is not even
    /// cloned. `None` here is what keeps the pass free for every normal file.
    #[test]
    fn a_file_without_duplicates_is_left_untouched() {
        let src = "mod a { pub trait Tr {} } mod b { pub trait Other {} } \
                   struct S; impl a::Tr for S {}";
        assert!(prune(src).expect("no duplicates").is_none());
    }

    /// THE REGRESSION. `impl real::Tr for S` names exactly one declaration, so
    /// the file must survive — with `decoy::Tr` gone, since nothing names it.
    #[test]
    fn a_qualified_impl_header_selects_its_declaration_and_prunes_the_other() {
        let src = "mod decoy { pub trait Tr { fn m(&self) -> u64; } } \
                   mod real { pub trait Tr { fn m(&self) -> u64; } } \
                   struct S; impl real::Tr for S { fn m(&self) -> u64 { 1 } }";
        let pruned = prune(src).expect("resolvable").expect("pruned");
        assert_eq!(
            surviving_module(&pruned, "Tr"),
            Some(vec!["real".to_string()])
        );
        // The whole point: the gate the pass feeds must now PASS.
        TraitScopeIndex::build(&pruned)
            .reject_duplicate_trait_names()
            .expect("the file has unique trait idents after pruning");
    }

    /// ORDER-INDEPENDENCE. The survivor is chosen by what the impl header NAMES,
    /// never by declaration order — the exact axis the cardinal defect turned on.
    #[test]
    fn the_survivor_does_not_depend_on_declaration_order() {
        let forward = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                       struct S; impl real::Tr for S {}";
        let reverse = "mod real { pub trait Tr {} } mod decoy { pub trait Tr {} } \
                       struct S; impl real::Tr for S {}";
        for src in [forward, reverse] {
            let pruned = prune(src).expect("resolvable").expect("pruned");
            assert_eq!(
                surviving_module(&pruned, "Tr"),
                Some(vec!["real".to_string()]),
                "{src}"
            );
        }
    }

    /// A `use` at the impl's scope disambiguates just as a qualifier does.
    #[test]
    fn a_use_binding_selects_the_declaration() {
        let src = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                   use real::Tr; struct S; impl Tr for S {}";
        let pruned = prune(src).expect("resolvable").expect("pruned");
        assert_eq!(
            surviving_module(&pruned, "Tr"),
            Some(vec!["real".to_string()])
        );
    }

    /// The RESOLVED ident decides, not the written one: under a rename the last
    /// segment is not even a duplicated ident, yet the impl still names one of
    /// the two declarations and must keep it — and the OTHER one.
    #[test]
    fn a_renamed_impl_header_still_selects_its_declaration() {
        let src = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                   use decoy::Tr as Other; struct S; impl Other for S {}";
        let pruned = prune(src).expect("resolvable").expect("pruned");
        assert_eq!(
            surviving_module(&pruned, "Tr"),
            Some(vec!["decoy".to_string()])
        );
    }

    /// An impl written INSIDE one of the modules resolves against its own scope.
    #[test]
    fn a_scope_relative_bare_impl_header_selects_its_own_module() {
        let src = "mod decoy { pub trait Tr {} } \
                   mod real { pub trait Tr {} pub struct S; impl Tr for S {} }";
        let pruned = prune(src).expect("resolvable").expect("pruned");
        assert_eq!(
            surviving_module(&pruned, "Tr"),
            Some(vec!["real".to_string()])
        );
    }

    /// FAIL CLOSED. Bare `impl Tr for S` with two candidates and no `use` is not
    /// even legal Rust (E0405); it must not be resolved by declaration order.
    #[test]
    fn a_bare_ambiguous_impl_header_fails_closed() {
        let src = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                   struct S; impl Tr for S {}";
        assert!(prune(src).is_err());
    }

    /// FAIL CLOSED. Both declarations are live, so no prune can make the
    /// bare-name key faithful.
    #[test]
    fn two_impls_naming_two_declarations_fail_closed() {
        let src = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                   struct A; struct B; impl decoy::Tr for A {} impl real::Tr for B {}";
        assert!(prune(src).is_err());
    }

    /// FAIL CLOSED. Nothing selects a survivor.
    #[test]
    fn duplicates_with_no_impl_at_all_fail_closed() {
        let src = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} }";
        assert!(prune(src).is_err());
    }

    /// THE BOUND REGRESSION. `append_trait_bounds` records the path's LAST
    /// SEGMENT, so `T: real::Tr` and `T: decoy::Tr` are the same string — but a
    /// bound that RESOLVES votes like an impl header does, and once every site
    /// agrees on one declaration the surviving last segment is faithful again.
    /// All five spellings of a `syn::TraitBound` are pinned.
    #[test]
    fn a_bound_agreeing_with_the_impl_header_selects_that_declaration() {
        let qualified = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                         struct S; impl real::Tr for S {} fn g<T: real::Tr>(_t: T) {}";
        let bare = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                    use real::Tr; struct S; impl real::Tr for S {} fn g<T: Tr>(_t: T) {}";
        let where_clause = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                            use real::Tr; struct S; impl real::Tr for S {} \
                            fn g<T>(_t: T) where T: Tr {}";
        let dyn_pos = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                       struct S; impl real::Tr for S {} fn takes(_t: &dyn real::Tr) {}";
        let impl_pos = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                        struct S; impl real::Tr for S {} fn takes(_t: impl real::Tr) {}";
        for src in [qualified, bare, where_clause, dyn_pos, impl_pos] {
            let pruned = prune(src)
                .unwrap_or_else(|e| panic!("{src}: {e}"))
                .expect("pruned");
            assert_eq!(
                surviving_module(&pruned, "Tr"),
                Some(vec!["real".to_string()]),
                "{src}"
            );
            TraitScopeIndex::build(&pruned)
                .reject_duplicate_trait_names()
                .unwrap_or_else(|e| panic!("{src}: {e}"));
        }
    }

    /// CARDINAL, and the reason a bound must VOTE rather than be ignored: with
    /// the impl naming `decoy::Tr` and the bound naming `real::Tr`, pruning to
    /// the impl's survivor would make the bound's `"Tr"` answer with `decoy`'s
    /// contract. Measured through the production CLI with this vote removed: a
    /// FALSE assertion verified while its TRUE twin did not.
    #[test]
    fn a_bound_disagreeing_with_the_impl_header_fails_closed() {
        let src = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                   struct D; impl decoy::Tr for D {} fn g<T: real::Tr>(_t: T) {}";
        assert!(prune(src).is_err());
    }

    /// FAIL CLOSED. A bound whose last segment is a duplicated ident but which
    /// resolves to NO in-file declaration cannot vote, and its last segment
    /// would still key to whoever survived. Both a bare `T: Tr` with two
    /// candidates (rustc rejects it too, E0405) and a qualifier that names no
    /// in-file module.
    #[test]
    fn an_unresolvable_bound_on_a_duplicated_ident_fails_closed() {
        let bare = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                    struct S; impl real::Tr for S {} fn g<T: Tr>(_t: T) {}";
        let absent = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                      struct S; impl real::Tr for S {} fn g<T: absent::Tr>(_t: T) {}";
        for src in [bare, absent] {
            assert!(prune(src).is_err(), "{src}");
        }
    }

    /// Supertraits are spelled as `TraitBound`s too, and `parse_trait_decl`
    /// records the same last segment — so they vote the same way.
    #[test]
    fn a_supertrait_votes_like_any_other_naming_site() {
        let agrees = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                      use real::Tr; pub trait Sub: Tr {} \
                      struct S; impl real::Tr for S {} impl Sub for S {}";
        let pruned = prune(agrees).expect("resolvable").expect("pruned");
        assert_eq!(
            surviving_module(&pruned, "Tr"),
            Some(vec!["real".to_string()])
        );

        let disagrees = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                         pub trait Sub: decoy::Tr {} \
                         struct S; impl real::Tr for S {} impl Sub for S {}";
        assert!(prune(disagrees).is_err());
    }

    /// A bound written INSIDE a module resolves against THAT module's scope, not
    /// the file root: `mod real { trait Sub: Tr {} }` names `real::Tr`.
    #[test]
    fn a_bound_resolves_from_the_module_that_wrote_it() {
        let src = "mod decoy { pub trait Tr {} } \
                   mod real { pub trait Tr {} pub trait Sub: Tr {} } \
                   struct S; impl real::Tr for S {}";
        let pruned = prune(src).expect("resolvable").expect("pruned");
        assert_eq!(
            surviving_module(&pruned, "Tr"),
            Some(vec!["real".to_string()])
        );

        // The same supertrait written in `decoy` votes for `decoy::Tr` and so
        // disagrees with the impl — order-independent, and not a coin flip.
        let split = "mod decoy { pub trait Tr {} pub trait Sub: Tr {} } \
                     mod real { pub trait Tr {} } \
                     struct S; impl real::Tr for S {}";
        assert!(prune(split).is_err());
    }

    /// A bound may be the ONLY naming site: it elects a survivor on its own.
    #[test]
    fn a_bound_alone_selects_a_survivor() {
        let src = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                   fn g<T: real::Tr>(_t: T) {}";
        let pruned = prune(src).expect("resolvable").expect("pruned");
        assert_eq!(
            surviving_module(&pruned, "Tr"),
            Some(vec!["real".to_string()])
        );
    }

    /// A RENAMED bound votes for the declaration it resolves to, exactly as a
    /// renamed impl header does — the written segment is not even a duplicate.
    #[test]
    fn a_renamed_bound_votes_for_its_declaration() {
        let src = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                   use decoy::Tr as Other; struct D; impl decoy::Tr for D {} \
                   fn g<T: Other>(_t: T) {}";
        let pruned = prune(src).expect("resolvable").expect("pruned");
        assert_eq!(
            surviving_module(&pruned, "Tr"),
            Some(vec!["decoy".to_string()])
        );

        let conflicting = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                           use decoy::Tr as Other; struct S; impl real::Tr for S {} \
                           fn g<T: Other>(_t: T) {}";
        assert!(prune(conflicting).is_err());
    }

    /// NARROWNESS for the bound rejection: a bound on a trait that is NOT
    /// duplicated must not be disturbed by a duplication elsewhere in the file.
    /// Without this pin the bound sweep could quietly become a blanket rejection
    /// of every file that has any duplicate.
    #[test]
    fn a_bound_on_a_unique_trait_is_unaffected_by_an_unrelated_duplicate() {
        let src = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                   pub trait Other {} struct S; impl real::Tr for S {} impl Other for S {} \
                   fn g<T: Other>(_t: T) {}";
        let pruned = prune(src).expect("resolvable").expect("pruned");
        assert_eq!(
            surviving_module(&pruned, "Tr"),
            Some(vec!["real".to_string()])
        );
        assert_eq!(surviving_module(&pruned, "Other"), Some(Vec::new()));
    }

    /// An UNANNOTATED impl keeps its declaration live just as an annotated one
    /// does — the receiver-kind registry and the trait-shape probes read every
    /// `impl <Trait> for T` block, not only `#[trust_vc::trait_impl]` ones.
    #[test]
    fn an_unannotated_impl_counts_as_a_reference() {
        let src = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                   struct A; struct B; \
                   impl decoy::Tr for A {} \
                   #[trust_vc::trait_impl] impl real::Tr for B {}";
        assert!(prune(src).is_err());
    }

    /// A foreign trait impl in the same file must not be mistaken for a
    /// reference to either duplicate.
    #[test]
    fn a_foreign_impl_header_does_not_select_a_survivor() {
        let src = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                   struct S; impl core::fmt::Debug for S {} impl real::Tr for S {}";
        let pruned = prune(src).expect("resolvable").expect("pruned");
        assert_eq!(
            surviving_module(&pruned, "Tr"),
            Some(vec!["real".to_string()])
        );
    }

    /// Three same-named declarations, one named: the other TWO go.
    #[test]
    fn every_unnamed_same_named_declaration_is_pruned() {
        let src = "mod a { pub trait Tr {} } mod b { pub trait Tr {} } mod c { pub trait Tr {} } \
                   struct S; impl b::Tr for S {}";
        let pruned = prune(src).expect("resolvable").expect("pruned");
        assert_eq!(surviving_module(&pruned, "Tr"), Some(vec!["b".to_string()]));
        assert_eq!(
            TraitScopeIndex::build(&pruned)
                .duplicate_trait_idents()
                .len(),
            0
        );
    }

    /// The type-side gate is independent and must keep firing through a prune.
    #[test]
    fn the_duplicate_type_gate_is_not_weakened_by_the_trait_prune() {
        let src = "mod decoy { pub trait Tr {} } mod real { pub trait Tr {} } \
                   mod inner { pub struct S; } pub struct S; impl real::Tr for S {}";
        let pruned = prune(src).expect("resolvable").expect("pruned");
        assert!(TraitScopeIndex::build(&pruned)
            .reject_duplicate_type_names()
            .is_err());
    }

    // -----------------------------------------------------------------------
    // `expanded_path_segments` — recognising a FOREIGN trait through a rename.
    // -----------------------------------------------------------------------

    fn expand(src: &str, scope: &[&str]) -> Vec<String> {
        let file = syn::parse_file(src).expect("parse");
        let item_impl = first_impl(src);
        let (_, path, _) = item_impl.trait_.as_ref().unwrap();
        let scope: Vec<String> = scope.iter().map(|s| (*s).to_string()).collect();
        TraitScopeIndex::build(&file).expanded_path_segments(&scope, path)
    }

    /// The measured `PartialEq` case: a rename must expand to the path the
    /// program imported, so a FOREIGN-trait NAME test still fires. `resolve_*`
    /// cannot answer this — `core::cmp::PartialEq` is declared in no file here.
    #[test]
    fn a_renamed_foreign_trait_expands_to_its_imported_path() {
        let src = "use core::cmp::PartialEq as Eq2; struct P; impl Eq2 for P {}";
        assert_eq!(
            expand(src, &[]).last().map(String::as_str),
            Some("PartialEq")
        );

        let chain = "mod mid { pub use core::cmp::PartialEq as P; } use mid::P as Q; \
                     struct R; impl Q for R {}";
        assert_eq!(
            expand(chain, &[]).last().map(String::as_str),
            Some("PartialEq")
        );
    }

    /// Expansion only ever substitutes what the program imported: an unbound
    /// head, and a leading-`::` path, come back unchanged.
    #[test]
    fn an_unimported_path_expands_to_itself() {
        let plain = "struct P; impl PartialEq for P {}";
        assert_eq!(expand(plain, &[]), vec!["PartialEq".to_string()]);

        let absolute = "struct P; impl ::core::cmp::PartialEq for P {}";
        assert_eq!(
            expand(absolute, &[]).last().map(String::as_str),
            Some("PartialEq")
        );

        let unrelated = "use core::cmp::Ordering; struct P; impl Ordering for P {}";
        assert_eq!(
            expand(unrelated, &[]).last().map(String::as_str),
            Some("Ordering")
        );
    }

    // -----------------------------------------------------------------------
    // `resolved_supertrait_names` — the supertrait cardinal.
    // -----------------------------------------------------------------------

    fn supertraits_of(src: &str, name: &str, scope: &[&str]) -> Vec<String> {
        fn find(items: &[syn::Item], name: &str) -> Option<syn::ItemTrait> {
            for item in items {
                match item {
                    syn::Item::Trait(t) if t.ident == name => return Some(t.clone()),
                    syn::Item::Mod(m) => {
                        if let Some((_, inner)) = &m.content {
                            if let Some(found) = find(inner, name) {
                                return Some(found);
                            }
                        }
                    }
                    _ => {}
                }
            }
            None
        }
        let file = syn::parse_file(src).expect("parse");
        let item_trait = find(&file.items, name).expect("the trait");
        let scope: Vec<String> = scope.iter().map(|s| (*s).to_string()).collect();
        resolved_supertrait_names(&TraitScopeIndex::build(&file), &scope, &item_trait)
    }

    /// A renamed supertrait names its DECLARATION, not the rename — and not a
    /// different trait that happens to bear the rename's spelling.
    #[test]
    fn a_renamed_supertrait_resolves_to_the_declaration() {
        let src = "mod origin { pub trait Base {} } use origin::Base as Alias; \
                   pub trait Derived: Alias {}";
        assert_eq!(
            supertraits_of(src, "Derived", &[]),
            vec!["Base".to_string()]
        );

        // The cardinal: `Peek` is ALSO an in-file trait, in a module the rename
        // does not name. Every declaration ident here is distinct.
        let cardinal = "mod origin { pub trait Counter {} } mod other { pub trait Peek {} } \
                        use origin::Counter as Peek; pub trait Derived: Peek {}";
        assert_eq!(
            supertraits_of(cardinal, "Derived", &[]),
            vec!["Counter".to_string()]
        );
    }

    /// NARROWNESS: unrenamed, module-local and FOREIGN supertraits keep their
    /// existing names, and an undecidable one is omitted rather than guessed.
    #[test]
    fn ordinary_supertraits_are_unchanged_and_undecidable_ones_are_omitted() {
        let plain = "pub trait Base {} pub trait Derived: Base {}";
        assert_eq!(
            supertraits_of(plain, "Derived", &[]),
            vec!["Base".to_string()]
        );

        let local = "mod m { pub trait Base {} pub trait Derived: Base {} }";
        assert_eq!(
            supertraits_of(local, "Derived", &["m"]),
            vec!["Base".to_string()]
        );

        let foreign = "pub trait Derived: Clone {}";
        assert_eq!(
            supertraits_of(foreign, "Derived", &[]),
            vec!["Clone".to_string()]
        );

        // Last segment names an in-file trait, but the path does not resolve to
        // it: keeping `"Base"` would attribute `m::Base`'s contract.
        let undecidable = "mod m { pub trait Base {} } pub trait Derived: absent::Base {}";
        assert!(supertraits_of(undecidable, "Derived", &[]).is_empty());
    }
}
