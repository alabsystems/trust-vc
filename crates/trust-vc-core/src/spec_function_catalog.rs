//! Source-only spec function catalog for VC extraction.
//!
//! This is intentionally narrower than proc-macro `#[trust_vc::spec]`
//! expansion: it supports sibling source spec functions in source files loaded
//! by `verify_function_from_file`.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use proc_macro2::Span;
use quote::quote;
use syn::fold::Fold;
use syn::visit::Visit;
use syn::visit_mut::VisitMut;

use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::TrustVcType;
use crate::ir_lowering::SOURCE_CATALOG_MATH_INT_MARKER;
use crate::local_vars::extract_type_string;
use crate::vc::{ProofObligation, VerificationContext};
use crate::VerifyResult;

#[derive(Debug, Clone)]
struct SpecParam {
    name: String,
    ty: TrustVcType,
}

#[derive(Debug, Clone)]
struct SpecFunctionDef {
    name: String,
    params: Vec<SpecParam>,
    return_ty: TrustVcType,
    body_condition: String,
    trigger: String,
    bound_vars: Vec<String>,
    is_opaque: bool,
    /// True for a Verus `uninterp spec fn f(x: int) -> bool;` — a spec function
    /// DECLARED with no body (see `tracked_syntax::mark_bodyless_spec_fns_uninterp`).
    ///
    /// It is declared as a helper symbol and NEVER given a defining axiom, so it
    /// is strictly uninterpreted. That is unconditional: unlike `is_opaque`, no
    /// `reveal!` can turn the body on, because there is no body to reveal.
    /// `body_condition` is left as the vacuous `f(x) == f(x)` so that even if a
    /// future refactor were to emit it, it would carry ZERO proof power rather
    /// than a fabricated definition.
    is_uninterp: bool,
    /// True when the source function carries `#[trust_vc::inline]`. Mirrors the
    /// proc-macro path's `.with_inline(...)` so file/source-catalog inline spec
    /// functions are call-site-substituted (setup.rs populates `inline_bodies`
    /// from inline body axioms) instead of relying on the #2655 demand-inline
    /// retry — which never re-encodes the goal for a datatype-selector body and
    /// leaves `getter_wrong`-shaped negative postconditions stuck at
    /// "quantifier-unhandled" Unknown. Part of #2777.
    is_inline: bool,
    /// True when this spec function participates in a recursive cycle (direct
    /// self-recursion, or a mutual `a -> b -> a` cycle) that is NOT PROVEN to
    /// terminate. A recursive cycle is proven terminating only if (1) every cycle
    /// member carries a `#[trust_vc::decreases]` clause AND (2) the declared
    /// measure is DISCHARGED — i.e. it strictly decreases (lexicographically, in
    /// the encoder's faithful arithmetic, so bit-vector wraparound and partial
    /// casts to `nat` are honored) on every recursive call under that call's path
    /// condition, with the caller components and the callee component witnessing
    /// the first strict decrease bounded below there.
    ///
    /// Merely CARRYING a `#[decreases]` attribute is insufficient: a bogus measure
    /// that does not actually shrink (e.g. `f(n) == f(n) + 1` with
    /// `#[decreases(n)]`, `#[decreases(7)]`, or `f(n) == f(n + 1) + 1`) yields a
    /// defining axiom `forall x. {f(x)} f(x) == body(x)` with NO model — the axiom
    /// system entails `false` and any goal mentioning `f` verifies vacuously
    /// (catastrophic false `Verified`). Likewise a contradictory mutual cycle
    /// (`f(n) == g(n) + 1`, `g(n) == f(n) + 1`). When this flag is set we leave
    /// `f` uninterpreted (helper declaration only, no defining axiom) so the engine
    /// fails closed instead of trusting a contradiction.
    ///
    /// Computed at the catalog level by [`SpecFunctionCatalog::recursion_suppresses_axiom`]
    /// because cycle membership spans multiple functions and the measure-decrease
    /// proof must cover every edge of the cycle.
    recursion_without_full_decreases: bool,
}

#[derive(Clone)]
struct SourceSpecFunction {
    item_fn: syn::ItemFn,
    #[cfg_attr(not(test), allow(dead_code))]
    recommends: Vec<String>,
}

#[derive(Default)]
pub(crate) struct SpecFunctionCatalog {
    specs: HashMap<String, SourceSpecFunction>,
    /// Exact Rust `use path::item as alias` bindings collected from the body
    /// currently being verified. The alias is a second spelling for the same
    /// function denotation; it is deliberately NOT represented by cloning the
    /// source body under a fresh symbol, which could bypass opacity or recursive
    /// termination admission. [`apply_spec_alias_by_name`](Self::apply_spec_alias_by_name)
    /// installs only an alias-equality bridge to the canonical symbol.
    exact_alias_targets: HashMap<String, String>,
    /// Memoizes the cycle-level termination verdict keyed by the canonical
    /// (sorted, comma-joined) cycle-member set, so the isolated solver query
    /// that proves the `decreases` measure actually shrinks is run at most once
    /// per recursive cycle even though the gate is consulted once per applied
    /// cycle member.
    termination_cache: RefCell<HashMap<String, TerminationCheck>>,
}

#[derive(Clone)]
enum TerminationCheck {
    Proven,
    /// The cycle cannot be admitted (a real decrease counterexample or a
    /// structurally unsupported/ill-formed definition), with no independent
    /// authority verdict to preserve.
    NotAdmitted,
    /// No model/refutation exists: proof authority was withheld (for example,
    /// strict AY replay rejected an unsupported theory step).
    Inconclusive(VerifyResult),
}

/// Converts the narrow Verus-style open spec spelling used by source-only
/// fixtures into Rust syntax that `syn` can parse.
pub(crate) fn normalize_open_spec_source(source: &str) -> String {
    // Apply the `spec fn` rewrites only to the CODE portion of each line (before
    // any `//` line comment). A blind `source.replace("spec fn", ...)` corrupts
    // the substring "spec fn" wherever it appears inside a comment (e.g.
    // `// a recursive spec fn`), turning it into broken code and failing the
    // parse. Line comments are the common case in source fixtures; block
    // comments / string literals containing "spec fn" are not handled here.
    let normalized = source
        .lines()
        .map(|line| {
            let (code, comment) = match line.find("//") {
                Some(idx) => (&line[..idx], &line[idx..]),
                None => (line, ""),
            };
            let code = code
                .replace("pub open spec fn", "#[trust_vc::spec]\npub fn")
                .replace("open spec fn", "#[trust_vc::spec]\nfn")
                .replace("pub spec fn", "#[trust_vc::spec]\npub fn")
                .replace("spec fn", "#[trust_vc::spec]\nfn");
            format!("{code}{comment}")
        })
        .collect::<Vec<_>>()
        .join("\n");

    normalize_spec_recommends_clauses(&normalize_named_return_types(&normalized))
}

fn normalize_named_return_types(source: &str) -> String {
    let mut out = String::with_capacity(source.len());
    let mut rest = source;

    while let Some(arrow_pos) = rest.find("->") {
        out.push_str(&rest[..arrow_pos]);
        out.push_str("->");

        let after_arrow = &rest[arrow_pos + 2..];
        let ws_len = after_arrow
            .char_indices()
            .find(|(_, ch)| !ch.is_whitespace())
            .map_or(after_arrow.len(), |(idx, _)| idx);
        let whitespace = &after_arrow[..ws_len];
        let after_ws = &after_arrow[ws_len..];

        if let Some(after_open) = after_ws.strip_prefix('(') {
            if let Some(close_pos) = after_open.find(')') {
                let inner = &after_open[..close_pos];
                if let Some((name, ty)) = inner.split_once(':') {
                    let name = name.trim();
                    let ty = ty.trim();
                    if is_ident_like(name) && !ty.is_empty() && !ty.contains(',') {
                        out.push_str(whitespace);
                        out.push_str(ty);
                        rest = &after_open[close_pos + 1..];
                        continue;
                    }
                }
            }
        }

        out.push_str(whitespace);
        rest = after_ws;
    }

    out.push_str(rest);
    out
}

fn normalize_spec_recommends_clauses(source: &str) -> String {
    let mut out = String::with_capacity(source.len());
    let mut cursor = 0;

    while let Some(spec_rel) = source[cursor..].find("#[trust_vc::spec]") {
        let spec_start = cursor + spec_rel;
        let Some(fn_start) = find_keyword_from(source, spec_start, "fn") else {
            break;
        };
        let Some(body_start) = source[fn_start..].find('{').map(|rel| fn_start + rel) else {
            break;
        };

        let header = &source[spec_start..body_start];
        let header_fn_start = fn_start - spec_start;
        let Some(recommends_start) = find_keyword_from(header, header_fn_start, "recommends")
        else {
            out.push_str(&source[cursor..body_start]);
            cursor = body_start;
            continue;
        };

        let condition = header[recommends_start + "recommends".len()..]
            .trim()
            .trim_end_matches(',')
            .trim();
        if condition.is_empty() {
            out.push_str(&source[cursor..body_start]);
            cursor = body_start;
            continue;
        }

        let insert_pos = header.find('\n').map_or(0, |idx| idx + 1);
        out.push_str(&source[cursor..spec_start]);
        out.push_str(&header[..insert_pos]);
        out.push_str("#[trust_vc::recommends(");
        out.push_str(condition);
        out.push_str(")]\n");
        out.push_str(header[insert_pos..recommends_start].trim_end());
        out.push('\n');
        cursor = body_start;
    }

    out.push_str(&source[cursor..]);
    out
}

fn find_keyword_from(source: &str, start: usize, keyword: &str) -> Option<usize> {
    let mut offset = start;
    while let Some(rel) = source[offset..].find(keyword) {
        let idx = offset + rel;
        let before = source[..idx].chars().next_back();
        let after = source[idx + keyword.len()..].chars().next();
        if !before.is_some_and(is_ident_char) && !after.is_some_and(is_ident_char) {
            return Some(idx);
        }
        offset = idx + keyword.len();
    }
    None
}

fn is_ident_like(value: &str) -> bool {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn is_ident_char(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphanumeric()
}

impl SpecFunctionCatalog {
    pub(crate) fn from_file(file: &syn::File) -> Self {
        let mut catalog = Self::default();
        catalog.collect_items(&file.items);
        catalog
    }

    /// Register unambiguous, lexically unshadowed block `use` aliases whose
    /// target is an exact spec-catalog key. Non-spec targets are ignored and
    /// continue through the ordinary sibling-helper lane.
    ///
    /// This records name identity only. It never copies a definition or grants
    /// body visibility, so an alias cannot bypass `opaque`, `uninterp`, or the
    /// recursive-decreases gate attached to the canonical spec function.
    pub(crate) fn register_exact_aliases(
        &mut self,
        aliases: &BTreeMap<String, String>,
    ) -> TrustVcResult<()> {
        for (alias, source_path) in aliases {
            if alias == source_path || !self.specs.contains_key(source_path) {
                continue;
            }

            // A body-local import can legally shadow a file-scope item with the
            // same spelling, but the current source lane has one solver symbol
            // per spelling. Equating that symbol with the import target would
            // also rewrite contract attributes and transitive spec bodies, whose
            // Rust scope still resolves the file-scope item. Reject the collision
            // until source names carry lexical-scope identity.
            if self.specs.contains_key(alias) {
                return Err(TrustVcError::Encoding {
                    context: "source spec function alias",
                    detail: format!(
                        "block use alias `{alias}` shadows a different source spec; \
                         scope-indexed alias symbols are not yet supported, so TrustVc \
                         fails closed instead of conflating the two functions"
                    ),
                });
            }

            self.exact_alias_targets
                .insert(alias.clone(), source_path.clone());
        }
        Ok(())
    }

    pub(crate) fn exact_alias_targets(&self) -> &HashMap<String, String> {
        &self.exact_alias_targets
    }

    /// Cross-file extension of [`from_file`](Self::from_file): in addition to the
    /// spec functions declared *in* `file`, resolve spec functions IMPORTED into
    /// `file` from other modules of the SAME crate — `use crate::m::f;`,
    /// `use self::m::f;`, `use super::m::f;`, groups (`{f, g}`), and globs
    /// (`use crate::m::*;`) — and register each under the (bare) name it is bound
    /// to at the call site, so the existing bare-name call-resolution machinery
    /// (and its opacity / `reveal!` / recursion gating) applies uniformly.
    ///
    /// SOUNDNESS (fail closed):
    /// - An imported name is registered ONLY when it resolves to EXACTLY ONE spec
    ///   function found by the crate walk. An unresolved import (a cross-CRATE
    ///   `use other_crate::...`, a typo, or a name with no matching `#[spec]` fn)
    ///   or an AMBIGUOUS one (e.g. two globbed modules each export a `mul`) is
    ///   left unregistered — the call then stays an uninterpreted symbol and the
    ///   obligation fails closed, never silently true.
    /// - A locally-declared spec fn always shadows an import of the same name
    ///   (we never overwrite a `from_file` entry).
    /// - Renamed imports (`use ... as other`) are NOT registered (the helper
    ///   symbol is keyed by the function's own ident; a mismatch would mis-bind),
    ///   so they fail closed rather than resolve to the wrong symbol.
    /// - Opacity is preserved exactly: the resolved def's `#[trust_vc::opaque]`
    ///   attribute travels with its `ItemFn`, so an imported opaque spec stays
    ///   uninterpreted until a `reveal!` in the verified body discloses its body
    ///   axiom — identical to an in-file opaque spec.
    ///
    /// Cross-CRATE resolution (e.g. `use trust_vc_std::arithmetic::mul`) is
    /// deliberately out of scope here: it needs compiled metadata / the
    /// rustc-driver front end and is handled, for the `cargo trust-vc check` CLI
    /// path, by the separate path-dependency spec importer.
    pub(crate) fn from_file_with_crate_imports(file: &syn::File, source_file: &Path) -> Self {
        let mut catalog = Self::from_file(file);
        catalog.merge_imported_crate_specs(file, source_file);
        catalog
    }

    /// Resolves the file's module-level `use` imports against a crate-wide index
    /// of `#[trust_vc::spec]` functions and registers the unambiguous matches.
    /// See [`from_file_with_crate_imports`](Self::from_file_with_crate_imports)
    /// for the soundness contract.
    fn merge_imported_crate_specs(&mut self, file: &syn::File, source_file: &Path) {
        // Resolve the crate root (and this file's module path within it).
        let Some(crate_root) = crate::mode_index::discover_crate_root(source_file) else {
            return;
        };
        let current_module = current_module_path(source_file, &crate_root);

        // Collect crate-relative imports from the file's MODULE-LEVEL `use` items.
        // (Imports nested inside inline submodules of this file are left for the
        // narrower in-file path; they simply stay unresolved here — fail closed.)
        let mut collector = SpecImportCollector {
            current_module,
            imports: Vec::new(),
        };
        for item in &file.items {
            if let syn::Item::Use(item_use) = item {
                let mut prefix = Vec::new();
                collector.collect_tree(&mut prefix, &item_use.tree);
            }
        }
        if collector.imports.is_empty() {
            // No crate-relative spec imports — skip the crate walk entirely so the
            // common (no-import) case costs nothing.
            return;
        }

        let Some(index) = get_or_build_crate_spec_index(&crate_root) else {
            return;
        };

        // Gather candidate source defs per in-scope name, tracking the set of
        // distinct (module, leaf) sources so we can fail closed on ambiguity.
        let mut candidates: HashMap<String, BTreeSet<(Vec<String>, String)>> = HashMap::new();
        let mut defs: HashMap<(Vec<String>, String), syn::ItemFn> = HashMap::new();
        for import in &collector.imports {
            match &import.leaf {
                Some(leaf) => {
                    let key = (import.module.clone(), leaf.clone());
                    if let Some(item_fn) = index.by_path.get(&key) {
                        candidates
                            .entry(import.in_scope_name.clone())
                            .or_default()
                            .insert(key.clone());
                        defs.insert(key, item_fn.clone());
                    }
                }
                None => {
                    // Glob: each spec fn in the module is imported under its own name.
                    if let Some(list) = index.by_module.get(&import.module) {
                        for (name, item_fn) in list {
                            let key = (import.module.clone(), name.clone());
                            candidates
                                .entry(name.clone())
                                .or_default()
                                .insert(key.clone());
                            defs.insert(key, item_fn.clone());
                        }
                    }
                }
            }
        }

        for (name, keys) in candidates {
            // Unambiguous resolution only.
            if keys.len() != 1 {
                continue;
            }
            // Never shadow a locally-declared spec fn.
            if self.specs.contains_key(&name) {
                continue;
            }
            let Some(key) = keys.into_iter().next() else {
                continue;
            };
            // The helper symbol is keyed by the function's own ident; only the
            // case where the in-scope name equals the def's ident binds correctly
            // (renamed imports are skipped — fail closed).
            if name != key.1 {
                continue;
            }
            if let Some(item_fn) = defs.get(&key) {
                self.specs.insert(
                    name,
                    SourceSpecFunction {
                        item_fn: item_fn.clone(),
                        recommends: recommends_conditions(&item_fn.attrs),
                    },
                );
            }
        }
    }

    fn collect_items(&mut self, items: &[syn::Item]) {
        // Top-level spec fns: registered under the bare ident regardless of
        // visibility (byte-identical to the historical behavior — a top-level fn is
        // in scope for the whole file).
        for item in items {
            if let syn::Item::Fn(item_fn) = item {
                if has_spec_attr(&item_fn.attrs) {
                    self.specs.insert(
                        item_fn.sig.ident.to_string(),
                        SourceSpecFunction {
                            item_fn: item_fn.clone(),
                            recommends: recommends_conditions(&item_fn.attrs),
                        },
                    );
                }
            }
        }

        // Spec fns nested inside inline modules: registered under the MODULE-QUALIFIED
        // key (e.g. `module_adt::is_four_doors`), which is exactly the `::`-joined name
        // `path_to_string` produces at a qualified call site, so caller-side lowering
        // (env.lookup_fn) resolves the return type + opacity-gated body axiom through
        // the same `apply_spec_by_name` path as a top-level spec fn.
        //
        // VISIBILITY (soundness): only `pub` nested fns are registered under an
        // externally-referable key — a private module spec fn stays encapsulated
        // (an external caller referencing it keeps failing closed), matching Verus's
        // closed-visibility rule.
        let mut nested: Vec<(String, String, syn::ItemFn)> = Vec::new();
        collect_nested_pub_spec_fns(&[], items, &mut nested);
        for (_, qualified_key, item_fn) in &nested {
            self.specs.insert(
                qualified_key.clone(),
                SourceSpecFunction {
                    item_fn: item_fn.clone(),
                    recommends: recommends_conditions(&item_fn.attrs),
                },
            );
        }

        // Deliberately do not synthesize a bare key for a nested function. A bare
        // call is meaningful only when Rust name resolution puts that item in scope;
        // global uniqueness is not lexical import provenance. Qualified calls remain
        // available through the keys registered above, while unresolved bare calls
        // fail closed.
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn recommends_for(&self, name: &str) -> Option<&[String]> {
        let name = self
            .exact_alias_targets
            .get(name)
            .map(String::as_str)
            .unwrap_or(name);
        self.specs
            .get(name)
            .map(|source_spec| source_spec.recommends.as_slice())
    }

    /// Seed `ctx` with EVERY catalogued spec function's definitional body axiom,
    /// forcibly REVEALED, for use in a throwaway checking context.
    ///
    /// Only for the broadcast-lemma contract check
    /// (`vc_extraction::suppress_unestablished_broadcast_lemma_axioms`), whose
    /// child context is DISCARDED — nothing here reaches a target's context, so
    /// no opacity is leaked to a caller.
    ///
    /// Revealing is what makes the check meaningful rather than vacuous. An
    /// `#[trust_vc::opaque]` spec fn contributes NO body axiom to an ordinary
    /// context, so a lemma asserting `bcf(x) == x` over an opaque `bcf` is
    /// indistinguishable from one asserting `bcf(x) == 42` — both are unprovable
    /// and both would be dropped, silently deleting every legitimate lemma over
    /// an opaque function. Judging the lemma against the TRUE definition
    /// separates them: the first verifies, the second is refuted.
    ///
    /// Sound because a definitional body axiom is a true fact about the function;
    /// opacity is an abstraction/performance control, not a soundness gate. Verus
    /// likewise lets a lemma body `reveal(f)` and publish the resulting fact.
    pub(crate) fn apply_all_specs_revealed(&self, ctx: &mut VerificationContext) {
        let revealed = RevealNames {
            top_level: self.specs.keys().cloned().collect(),
            scoped: BTreeSet::new(),
        };
        let mut applied = BTreeSet::new();
        let mut applying = BTreeSet::new();
        let concrete_carriers = HashMap::new();
        let names: Vec<String> = self.specs.keys().cloned().collect();
        for name in names {
            // Best effort: a spec that cannot be applied simply contributes no
            // axiom, which can only make the CHECK stricter (an unestablished
            // lemma is dropped). It can never admit a lemma that should fail.
            let _ = self.apply_spec_by_name(
                &name,
                ctx,
                &mut applied,
                &mut applying,
                &revealed,
                &concrete_carriers,
            );
        }
    }

    pub(crate) fn apply_referenced_specs(
        &self,
        func: &syn::ItemFn,
        ctx: &mut VerificationContext,
    ) -> TrustVcResult<()> {
        let mut applied = BTreeSet::new();
        let mut applying = BTreeSet::new();
        let mut revealed = revealed_names_in_block(&func.block);
        // Visibility directives use the source spelling while defining body
        // axioms use the canonical catalog key. Normalize both query-level and
        // assert-by-scoped reveals before any function is applied so an alias
        // cannot disclose too much (or leave a scoped reveal ineffective).
        for (alias, canonical) in &self.exact_alias_targets {
            if revealed.top_level.contains(alias) {
                revealed.top_level.insert(canonical.clone());
            }
            if revealed.scoped.contains(alias) {
                revealed.scoped.insert(canonical.clone());
            }
        }
        // Per-instantiation monomorphization map: each generic recursive
        // datatype's base name → the concrete carrier (e.g. "GList" →
        // GList<i32>) inferred from the constructor calls the verified function
        // (and sibling spec fns) actually build. A generic spec fn over
        // `GList<T>` is then monomorphized to that carrier so its helper/axiom
        // sort matches the value carrier the lowering produces.
        let ConcreteCarrierAnalysis {
            carriers: concrete_carriers,
            conflicting_recursive_bases,
        } = self.collect_concrete_enum_carriers(func, ctx);
        // The verified function builds a generic self-recursive datatype at two or
        // more distinct concrete instantiations (e.g. both `GList<i32>` and
        // `GList<bool>`). The base cannot collapse to one per-instantiation carrier,
        // so its concrete alias is never registered and the nested-recursion
        // lowering would mix a concrete outer carrier with a template-sorted
        // recursive tail — a backend sort mismatch swallowed as a `SolverPanic`.
        // Record a clean fail-close signal so `prepare_context` returns a
        // `VerifyResult::Error` BEFORE any malformed query is built. Sound (never a
        // false `Verified`); merely incomplete versus Verus's per-instantiation
        // monomorphization.
        if !conflicting_recursive_bases.is_empty() {
            let bases = conflicting_recursive_bases
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .join(", ");
            ctx.generic_instantiation_conflict.get_or_insert_with(|| {
                format!(
                    "generic self-recursive datatype used at multiple distinct \
                     instantiations in one function (base(s): {bases}); cannot \
                     monomorphize to a single carrier — fail closed (sound, incomplete)"
                )
            });
        }
        // Register each inferred concrete per-instantiation carrier (`GList<i32>`)
        // as a CONCRETE source type alias so its constructor/selector metadata is
        // available to lowering even when the generic enum is used purely via
        // construction (e.g. `GTree::GBranch(..) != GTree::GLeaf(..)`) with no
        // spec fn taking it as a parameter. Concrete carriers carry no
        // `TypeParam`, so (unlike the template) they DO register variant metadata
        // in `build_type_env`, and their base-name-disjoint names never collide
        // with the metadata-suppressed template carrier.
        for carrier in concrete_carriers.values() {
            if let TrustVcType::Datatype { name, .. } = carrier {
                ctx.register_source_type_alias(name, carrier.clone());
            }
        }
        // Contract attributes are outside the function body's import scope.
        // Resolve them only through canonical catalog names; a body alias must
        // never retarget an `ensures(alias())` or `requires(alias())` clause.
        for name in referenced_contract_call_names(func) {
            self.apply_spec_by_name(
                &name,
                ctx,
                &mut applied,
                &mut applying,
                &revealed,
                &concrete_carriers,
            )?;
        }
        // Body calls may use an exact outer-block import alias. Apply that alias
        // only at this root call edge. Recursive dependencies are resolved by
        // `apply_spec_by_name` in their own source scope and therefore never
        // consult the target function's alias table.
        for name in called_names_in_block(&func.block) {
            if self.exact_alias_targets.contains_key(&name) {
                self.apply_spec_alias_by_name(
                    &name,
                    ctx,
                    &mut applied,
                    &mut applying,
                    &revealed,
                    &concrete_carriers,
                )?;
            } else {
                self.apply_spec_by_name(
                    &name,
                    ctx,
                    &mut applied,
                    &mut applying,
                    &revealed,
                    &concrete_carriers,
                )?;
            }
        }
        Ok(())
    }

    fn apply_spec_alias_by_name(
        &self,
        name: &str,
        ctx: &mut VerificationContext,
        applied: &mut BTreeSet<String>,
        applying: &mut BTreeSet<String>,
        revealed: &RevealNames,
        concrete_carriers: &HashMap<String, TrustVcType>,
    ) -> TrustVcResult<()> {
        if applied.contains(name) {
            return Ok(());
        }
        let canonical_name =
            self.exact_alias_targets
                .get(name)
                .cloned()
                .ok_or_else(|| TrustVcError::Encoding {
                    context: "source spec function alias",
                    detail: format!("missing canonical target for exact alias `{name}`"),
                })?;
        if !applying.insert(name.to_string()) {
            return Ok(());
        }

        self.apply_spec_by_name(
            &canonical_name,
            ctx,
            applied,
            applying,
            revealed,
            concrete_carriers,
        )?;

        let source_spec =
            self.specs
                .get(&canonical_name)
                .ok_or_else(|| TrustVcError::Encoding {
                    context: "source spec function alias",
                    detail: format!(
                        "exact alias `{name}` lost canonical target `{canonical_name}`"
                    ),
                })?;
        let suppress_recursive_axiom = self.recursion_suppresses_axiom(&canonical_name, ctx);
        let canonical_def = SpecFunctionDef::from_item_fn(
            &source_spec.item_fn,
            &canonical_name,
            ctx,
            suppress_recursive_axiom,
            concrete_carriers,
        )?;
        canonical_def.apply_alias_to_context(name, &canonical_name, ctx)?;

        applying.remove(name);
        applied.insert(name.to_string());
        Ok(())
    }

    pub(crate) fn apply_explicit_spec(
        &self,
        name: &str,
        ctx: &mut VerificationContext,
    ) -> TrustVcResult<bool> {
        let mut applied = BTreeSet::new();
        let mut applying = BTreeSet::new();
        let revealed = RevealNames::default();
        let concrete_carriers = HashMap::new();
        self.apply_spec_by_name(
            name,
            ctx,
            &mut applied,
            &mut applying,
            &revealed,
            &concrete_carriers,
        )?;
        Ok(applied.contains(name))
    }

    fn apply_spec_by_name(
        &self,
        name: &str,
        ctx: &mut VerificationContext,
        applied: &mut BTreeSet<String>,
        applying: &mut BTreeSet<String>,
        revealed: &RevealNames,
        concrete_carriers: &HashMap<String, TrustVcType>,
    ) -> TrustVcResult<()> {
        if applied.contains(name) {
            return Ok(());
        }

        let Some(source_spec) = self.specs.get(name) else {
            return Ok(());
        };
        let item_fn = &source_spec.item_fn;
        // B5 — mutual-recursion keystone: re-entering a name already on the
        // `applying` stack means we have closed a dependency cycle
        // `a -> ... -> a` (mutual or direct recursion). This used to hard-error,
        // which left every mutually recursive spec unusable. Instead we stop the
        // recursion here (the node is already being applied higher in the stack)
        // and let each cycle member install its helper declaration and — only when
        // the WHOLE cycle is termination-guarded by `decreases` — its defining
        // forall axiom. The soundness gate lives in `recursion_suppresses_axiom`
        // (consumed below), so cycle re-entry itself is not an error.
        if !applying.insert(name.to_string()) {
            return Ok(());
        }

        for dependency in called_names_in_block(&item_fn.block) {
            if dependency != name && self.specs.contains_key(&dependency) {
                self.apply_spec_by_name(
                    &dependency,
                    ctx,
                    applied,
                    applying,
                    revealed,
                    concrete_carriers,
                )?;
            }
        }

        // Compute the cycle-level soundness gate from the FULL catalog (a single
        // function's body cannot see whether a mutual partner carries `decreases`,
        // and the measure-decrease proof must cover every edge of the cycle). The
        // context supplies the parameter types (and type aliases) the isolated
        // termination query needs.
        let suppress_recursive_axiom = self.recursion_suppresses_axiom(name, ctx);
        let def = SpecFunctionDef::from_item_fn(
            item_fn,
            name,
            ctx,
            suppress_recursive_axiom,
            concrete_carriers,
        )?;
        def.apply_to_context(
            ctx,
            revealed.top_level.contains(name),
            revealed.scoped.contains(name),
        );
        applying.remove(name);
        applied.insert(name.to_string());
        Ok(())
    }

    /// Builds the per-instantiation monomorphization map: each generic enum's
    /// base name (`GList`) → the concrete carrier (`GList<i32>`) inferred from
    /// the constructor calls the verified function — and every sibling spec fn —
    /// actually build. First fully-inferred instantiation per base name wins; a
    /// base that resolves to more than one instantiation (or none) is left out,
    /// so the corresponding generic spec fn stays uninterpreted (sound, just
    /// incomplete) rather than being monomorphized to the wrong carrier.
    fn collect_concrete_enum_carriers(
        &self,
        func: &syn::ItemFn,
        ctx: &VerificationContext,
    ) -> ConcreteCarrierAnalysis {
        let mut out: HashMap<String, TrustVcType> = HashMap::new();
        let mut conflicting: BTreeSet<String> = BTreeSet::new();
        // First pass — the VERIFIED FUNCTION's body. Track which self-recursive
        // bases it constructs so we can tell whether a later-detected conflict is
        // one the function itself emits (and must therefore fail closed on).
        let mut func_recursive_bases: BTreeSet<String> = BTreeSet::new();
        {
            let mut collector = ConcreteCarrierCollector {
                ctx,
                out: &mut out,
                conflicting: &mut conflicting,
                recursive_bases: Some(&mut func_recursive_bases),
            };
            collector.visit_block(&func.block);
        }
        // Second pass — sibling spec-fn bodies. These widen `out`/`conflicting`
        // (so a generic helper used at a single instantiation anywhere still
        // monomorphizes) but never widen the function's fail-close set.
        {
            let mut collector = ConcreteCarrierCollector {
                ctx,
                out: &mut out,
                conflicting: &mut conflicting,
                recursive_bases: None,
            };
            for source_spec in self.specs.values() {
                collector.visit_block(&source_spec.item_fn.block);
            }
        }
        for base in &conflicting {
            out.remove(base);
        }
        // A self-recursive base the verified function builds AND that resolved to
        // more than one concrete instantiation: the function's own query would mix
        // a concrete outer carrier with a template-sorted recursive tail. Surface
        // it so `apply_referenced_specs` can fail closed cleanly.
        let conflicting_recursive_bases: BTreeSet<String> = func_recursive_bases
            .intersection(&conflicting)
            .cloned()
            .collect();
        ConcreteCarrierAnalysis {
            carriers: out,
            conflicting_recursive_bases,
        }
    }

    /// Same-file spec functions that `name`'s body calls (its outgoing edges in
    /// the spec-function call graph). Only bare-name siblings present in this
    /// catalog count as edges; unknown or qualified calls are not modeled here
    /// (they are handled, or fail closed, elsewhere).
    fn spec_dependencies(&self, name: &str) -> BTreeSet<String> {
        match self.specs.get(name) {
            Some(source_spec) => called_names_in_block(&source_spec.item_fn.block)
                .into_iter()
                .filter(|dependency| self.specs.contains_key(dependency))
                .collect(),
            None => BTreeSet::new(),
        }
    }

    /// SOUNDNESS GATE (B5): decide whether `name`'s defining forall axiom must be
    /// suppressed because `name` participates in a recursive cycle that is NOT
    /// PROVEN to terminate.
    ///
    /// A spec function's defining axiom `forall x. {f(x)} f(x) == body(x)` is a
    /// faithful equation only if the recursion it encodes terminates; an
    /// ill-founded recursion can make the equation system contradictory (e.g.
    /// `f(n) == f(n) + 1`, the mutual `f(n) == g(n) + 1` / `g(n) == f(n) + 1`, or
    /// `f(n: nat) == f((n - 1) as nat) + 1` with no base case), which entails
    /// `false` and lets ANY goal mentioning `f` verify vacuously — a catastrophic
    /// false `Verified`.
    ///
    /// Verus admits a recursive definition's axiom only after DISCHARGING a
    /// `decreases` termination proof. We do the same in two stages:
    ///
    /// 1. STRUCTURAL: every member of the cycle must carry a `#[decreases]` clause
    ///    and be present in this catalog (a missing member cannot be vouched for).
    ///    Otherwise fail closed.
    /// 2. SEMANTIC: the declared measure must actually shrink. We emit, into an
    ///    ISOLATED verification context that does NOT contain the (possibly
    ///    contradictory) defining axiom, a `MeasureDecreases` obligation for every
    ///    recursive call edge — `path_condition ==> (measure(callee_args) <
    ///    measure(caller_params))` in the component-wise well-founded
    ///    lexicographic order, plus non-negativity of the caller components —
    ///    and discharge it with the real solver. The callee component's bound is
    ///    load-bearing: `nat - nat` is
    ///    `int`-typed in Verus, and a partial `(n - 1) as nat` at `n == 0` must
    ///    not make an unbounded descent look well-founded. Because the obligations
    ///    use the engine's faithful arithmetic, bit-vector wraparound and partial
    ///    `nat` casts are honored. Only a `Verified` isolated query admits the
    ///    recursive axiom.
    ///
    /// Returns `true` to suppress the axiom (fail closed), `false` to emit it.
    fn recursion_suppresses_axiom(&self, name: &str, ctx: &mut VerificationContext) -> bool {
        // Cycle members of `name`: nodes reachable from `name` that can also reach
        // back to `name` — the strongly-connected component of `name`. A single
        // node with no self-edge is non-recursive and triggers no gate.
        let forward = self.reachable_from(name);
        let backward = self.reachable_into(name);
        let cycle: BTreeSet<&String> = forward.intersection(&backward).collect();

        let has_self_edge = self.spec_dependencies(name).contains(name);
        let is_recursive = has_self_edge || cycle.iter().any(|member| *member != name);
        if !is_recursive {
            return false;
        }

        // Stage 1 — structural: fail closed unless EVERY cycle member carries a
        // `decreases` clause and lives in this catalog.
        let structurally_guarded = cycle.iter().all(|member| match self.specs.get(*member) {
            Some(source_spec) => has_decreases_attr(&source_spec.item_fn.attrs),
            None => false,
        });
        if !structurally_guarded {
            return true;
        }

        // Stage 2 — semantic: the measure must be PROVEN to strictly decrease.
        // Suppress unless the isolated termination query succeeds. Preserve an
        // inconclusive authority verdict on the parent context: discarding it
        // would turn an unproven definition into an uninterpreted helper and let
        // a later SAT model masquerade as a refutation of the authored spec.
        match self.cycle_termination_check(&cycle, ctx) {
            TerminationCheck::Proven => false,
            TerminationCheck::NotAdmitted => true,
            TerminationCheck::Inconclusive(result) => {
                ctx.record_source_catalog_termination_failure(result);
                true
            }
        }
    }

    /// Stage-2 termination proof for a recursive cycle (memoized per cycle).
    ///
    /// Returns `Proven` only when every recursive edge is discharged. A concrete
    /// decrease counterexample or structurally unmodelable definition returns
    /// `NotAdmitted`; an authority/incompleteness verdict is preserved verbatim
    /// as `Inconclusive`. Every non-`Proven` result suppresses the body axiom.
    fn cycle_termination_check(
        &self,
        cycle: &BTreeSet<&String>,
        ctx: &VerificationContext,
    ) -> TerminationCheck {
        let mut members: Vec<String> = cycle.iter().map(|member| (*member).to_string()).collect();
        members.sort();
        let cache_key = members.join(",");
        if let Some(verdict) = self.termination_cache.borrow().get(&cache_key) {
            return verdict.clone();
        }
        let verdict = self.prove_cycle_terminates(&members, ctx);
        self.termination_cache
            .borrow_mut()
            .insert(cache_key, verdict.clone());
        verdict
    }

    fn prove_cycle_terminates(
        &self,
        members: &[String],
        ctx: &VerificationContext,
    ) -> TerminationCheck {
        // Recover each member's parameters, return type, and parsed measure.
        let mut infos: HashMap<&str, MemberTermInfo> = HashMap::new();
        for member in members {
            let Some(source_spec) = self.specs.get(member) else {
                return TerminationCheck::NotAdmitted;
            };
            let Some(info) = MemberTermInfo::from_spec(&source_spec.item_fn, ctx) else {
                return TerminationCheck::NotAdmitted;
            };
            infos.insert(member.as_str(), info);
        }
        let member_set: BTreeSet<String> = members.iter().cloned().collect();
        // Every member's recursive edges must discharge. Each member is checked in
        // its OWN isolated context (its parameters are the free variables), so
        // mutual partners with clashing parameter names never collide.
        aggregate_termination_checks(
            members
                .iter()
                .map(|caller| member_edges_decrease(caller, &infos, &member_set)),
        )
    }

    /// All catalog specs reachable from `name` along dependency edges, including
    /// `name` itself.
    fn reachable_from(&self, name: &str) -> BTreeSet<String> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![name.to_string()];
        while let Some(current) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            for dependency in self.spec_dependencies(&current) {
                if !seen.contains(&dependency) {
                    stack.push(dependency);
                }
            }
        }
        seen
    }

    /// All catalog specs that can reach `name` along dependency edges, including
    /// `name` itself (reverse reachability over the call graph).
    fn reachable_into(&self, name: &str) -> BTreeSet<String> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![name.to_string()];
        while let Some(current) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            for candidate in self.specs.keys() {
                if !seen.contains(candidate) && self.spec_dependencies(candidate).contains(&current)
                {
                    stack.push(candidate.clone());
                }
            }
        }
        seen
    }
}

/// Per-member data the cycle termination proof needs: the parameters (free
/// variables of the isolated query), the return type (so the function can be
/// declared as an uninterpreted helper when a substituted measure mentions a
/// recursive call), the parsed `decreases` measure expression(s), and the body
/// (scanned for recursive call edges).
struct MemberTermInfo {
    params: Vec<SpecParam>,
    return_ty: TrustVcType,
    measures: Vec<syn::Expr>,
    body: syn::Block,
}

impl MemberTermInfo {
    fn from_spec(item_fn: &syn::ItemFn, ctx: &VerificationContext) -> Option<Self> {
        let params = spec_params(&item_fn.sig, ctx).ok()?;
        if params.iter().any(|param| param.ty.contains_opaque()) {
            return None;
        }
        let return_ty = spec_return_type(&item_fn.sig, ctx).ok()?;
        if return_ty.contains_opaque() {
            return None;
        }
        let measures = decreases_measure_exprs(&item_fn.attrs)?;
        Some(Self {
            params,
            return_ty,
            measures,
            body: (*item_fn.block).clone(),
        })
    }

    /// Reconstruct a `MemberTermInfo` from a raw source function (a proof/exec fn on
    /// the file-extraction path, which is NOT in the spec catalog). Fail-closed:
    /// returns `None` for any shape the isolated measure query cannot model — a
    /// `self` receiver, any reference (`&T`/`&mut T`) parameter, generics, an
    /// opaque/unregistered parameter or return type, or a missing/unparseable
    /// `decreases` measure. The file-path caller treats `None` as "cannot analyze —
    /// fall back to the structural Stage-1 gate", so `None` NEVER causes
    /// over-rejection; it only means the semantic Stage-2 catch is skipped for that
    /// cycle.
    fn from_source_fn(
        sig: &syn::Signature,
        attrs: &[syn::Attribute],
        block: &syn::Block,
        ctx: &VerificationContext,
    ) -> Option<Self> {
        // An inherent/trait method with a shared or by-value receiver is
        // analyzable: the receiver does not participate in a value-parameter
        // `decreases` measure (the common `decreases(n)` shape), and its recursive
        // self-call `self.m(n-1)` is captured by `RecursiveCallScan`'s method-call
        // edge (matching the SCC's method-name edge model). A `&mut self` receiver
        // is rejected (its mutation could interact with the measure) — conservative
        // over-rejection. A measure that references `self` renders an undeclared
        // variable in the isolated query and fails the decrease check CLOSED, so
        // self-based measures stay suppressed without a special case.
        if let Some(receiver) = sig.receiver() {
            if receiver.mutability.is_some() {
                return None;
            }
        }
        if !sig.generics.params.is_empty() {
            return None;
        }
        for input in &sig.inputs {
            if let syn::FnArg::Typed(pat_type) = input {
                if matches!(&*pat_type.ty, syn::Type::Reference(_)) {
                    return None;
                }
            }
        }
        let params = member_value_params(sig, ctx).ok()?;
        if params.iter().any(|param| param.ty.contains_opaque()) {
            return None;
        }
        // Unlike catalog spec fns (which always declare a return type), a proof/exec
        // fn commonly returns unit (no `-> T`) — model that as `Unit` rather than
        // failing closed, or every unit-returning proof-fn cycle would skip Stage-2.
        let return_ty = match &sig.output {
            syn::ReturnType::Default => TrustVcType::Unit,
            syn::ReturnType::Type(..) => {
                let ty = spec_return_type(sig, ctx).ok()?;
                if ty.contains_opaque() {
                    return None;
                }
                ty
            }
        };
        let measures = decreases_measure_exprs(attrs)?;
        Some(Self {
            params,
            return_ty,
            measures,
            body: block.clone(),
        })
    }
}

/// Stage-2 semantic termination check for a recursion cycle discovered on the
/// file-extraction path (proof/exec fns, outside the spec catalog). Reconstructs
/// each member's [`MemberTermInfo`] from its source signature/attrs/body and runs
/// the SAME per-edge decrease proof the catalog uses in
/// [`SpecFunctionCatalog::prove_cycle_terminates`].
///
/// Returns:
/// - `Some(true)`  — every member modeled and every recursive edge strictly
///   decreases (well-founded; do NOT suppress).
/// - `Some(false)` — every member modeled but some edge does not decrease (the
///   declared measure is not a valid per-edge termination measure; the caller
///   suppresses fail-closed).
/// - `None`        — at least one member could not be modeled. Callers must treat
///   this as a failed termination proof and suppress the recursive axiom; the mere
///   presence of a `#[decreases]` attribute is not evidence of well-foundedness.
pub(crate) fn source_cycle_terminates(
    members: &[(String, syn::Signature, Vec<syn::Attribute>, syn::Block)],
    ctx: &VerificationContext,
) -> Option<bool> {
    let mut infos: HashMap<&str, MemberTermInfo> = HashMap::new();
    for (name, sig, attrs, block) in members {
        let info = MemberTermInfo::from_source_fn(sig, attrs, block, ctx)?;
        infos.insert(name.as_str(), info);
    }
    let member_set: BTreeSet<String> = members.iter().map(|(name, ..)| name.clone()).collect();
    Some(matches!(
        aggregate_termination_checks(members.iter().map(|(caller, ..)| member_edges_decrease(
            caller,
            &infos,
            &member_set
        )),),
        TerminationCheck::Proven
    ))
}

fn aggregate_termination_checks(
    checks: impl IntoIterator<Item = TerminationCheck>,
) -> TerminationCheck {
    let mut inconclusive = None;
    for check in checks {
        match check {
            TerminationCheck::Proven => {}
            TerminationCheck::NotAdmitted => return TerminationCheck::NotAdmitted,
            TerminationCheck::Inconclusive(result) => {
                inconclusive.get_or_insert(result);
            }
        }
    }
    inconclusive.map_or(TerminationCheck::Proven, TerminationCheck::Inconclusive)
}

/// A recursive call edge discovered in a member's body, together with the path
/// condition (conjunction of `if` guards) under which the call executes and the
/// enclosing constructor match-arm bindings (outermost first).
struct RecursiveEdge {
    callee: String,
    args: Vec<syn::Expr>,
    path: Vec<String>,
    arms: Vec<ArmBinding>,
}

/// A constructor `match`-arm in scope at a recursive call site. Captures the
/// matched scrutinee (a bare identifier), the variant constructor path exactly
/// as written, and the per-field sub-pattern binders (`Some(ident)` for an `x`
/// binder, `None` for `_`/non-ident). The decrease query reconstructs this into
/// the structural equation `scrutinee == Ctor(fields...)` and the field-variable
/// declarations it needs, so that the trusted `dt_size` constructor recurrence
/// (`size(Ctor(.., child, ..)) == 1 + size(child) + ...`) can fire and link the
/// scrutinee's size to its structural children.
///
/// Only flat tuple-struct constructor patterns over a recursive-datatype
/// scrutinee are modeled; anything else yields no binding (fail closed — the edge
/// is left without a structural equation, so its decrease stays unprovable).
#[derive(Clone)]
struct ArmBinding {
    scrutinee: String,
    constructor_path: syn::Path,
    field_pats: Vec<Option<String>>,
}

/// Proves that every recursive call in `caller`'s body strictly decreases the
/// declared `decreases` measure, by discharging a real solver query in an
/// ISOLATED context that does NOT contain `caller`'s (possibly contradictory)
/// defining axiom.
///
/// For each edge `caller -> callee(args)` reachable under path condition `P`, we
/// assert
///
/// ```text
/// P ==> ( measure_callee[params := args] <_wf_lex measure_caller(params)
///         && 0 <= measure_caller(params)
/// ```
///
/// Each integer component of `<_wf_lex` is `0 <= new && new < old`; only the
/// component witnessing the first strict decrease is consulted. The comparison
/// is encoded in the engine's faithful arithmetic, so a measure that wraps
/// (bit-vector) or leaves the well-founded `nat` range through a partial cast —
/// exactly how the bogus `f(n) == f(n) + 1` and unguarded
/// `f(n: nat) == f((n - 1) as nat) + 1` definitions fail to terminate — does NOT
/// discharge, and the axiom is suppressed. Returns `Proven` only when the
/// isolated query is `Verified`; preserves an inconclusive authority verdict.
fn member_edges_decrease(
    caller: &str,
    infos: &HashMap<&str, MemberTermInfo>,
    members: &BTreeSet<String>,
) -> TerminationCheck {
    let Some(caller_info) = infos.get(caller) else {
        return TerminationCheck::NotAdmitted;
    };
    let parameter_names: BTreeSet<&str> = caller_info
        .params
        .iter()
        .map(|param| param.name.as_str())
        .collect();
    if block_binds_any_name(&caller_info.body, &parameter_names) {
        // The termination query currently models caller parameters but not
        // arbitrary local bindings. A local/closure/match binding that shadows
        // one of those parameters would make rendered guards or recursive-call
        // arguments ambiguous. Refuse the definition rather than accidentally
        // interpreting the local as the entry parameter.
        return TerminationCheck::NotAdmitted;
    }

    let mut scan = RecursiveCallScan {
        members,
        path: Vec::new(),
        arms: Vec::new(),
        calls: Vec::new(),
    };
    scan.visit_block(&caller_info.body);
    // A genuine cycle member always recurses through at least one bare-name edge
    // (that is how the SCC edge was discovered). Finding none means we cannot
    // account for the recursion — fail closed.
    if scan.calls.is_empty() {
        return TerminationCheck::NotAdmitted;
    }

    let mut ctx = VerificationContext::new();
    for param in &caller_info.params {
        if ctx.get_variable_type(&param.name).is_none() {
            ctx.declare_var_typed(&param.name, param.ty.clone());
        }
    }
    // Declare every cycle member as an uninterpreted helper so a substituted
    // callee measure that itself mentions a recursive call (e.g. Ackermann's
    // nested `ack(m, n - 1)`) still encodes.
    for (name, info) in infos {
        let helper_params = info
            .params
            .iter()
            .map(|param| (param.name.clone(), param.ty.clone()))
            .collect();
        ctx.declare_helper_function_typed(name, info.return_ty.clone(), helper_params);
    }

    // The caller's own parameters, by name, used to shape datatype-typed measure
    // components into `dt_size(_)` and to type-resolve match-arm scrutinees.
    let caller_params: HashMap<&str, &TrustVcType> = caller_info
        .params
        .iter()
        .map(|param| (param.name.as_str(), &param.ty))
        .collect();

    // Shape the caller (old) measure: a direct recursive-datatype parameter `n`
    // becomes `__trust_vc_dt_size(n)` (a real arithmetic measure backed by the
    // trusted acyclicity invariant), every other component is rendered verbatim.
    let old_components: Vec<String> = caller_info
        .measures
        .iter()
        .map(|measure| shape_caller_component(measure, &caller_params))
        .collect();
    let old_measure = render_component_tuple(&old_components);
    let caller_nonneg = old_components
        .iter()
        .map(|component| format!("0 <= {component}"))
        .collect::<Vec<_>>()
        .join(" && ");

    // Arm-binding field variables already declared in this isolated context, so a
    // binder shared across arms is declared once (and a same-name/different-type
    // clash fails closed).
    let mut declared_bindings: HashMap<String, TrustVcType> = HashMap::new();

    for (index, edge) in scan.calls.iter().enumerate() {
        let Some(callee_info) = infos.get(edge.callee.as_str()) else {
            return TerminationCheck::NotAdmitted;
        };
        // Cannot map arguments onto the callee's parameters, or compare measures
        // of different lexicographic arity — fail closed.
        if edge.args.len() != callee_info.params.len() {
            return TerminationCheck::NotAdmitted;
        }
        if caller_info.measures.len() != callee_info.measures.len() {
            return TerminationCheck::NotAdmitted;
        }

        // Reconstruct the structural equation(s) for the constructor match-arms
        // enclosing this edge (`n == Succ(p)`), declaring each field binder, and
        // collect the binder names whose `*p` derefs are transparent (the `Box`
        // around a recursive child is erased: `*p` IS the child `p`).
        let mut arm_equations: Vec<String> = Vec::new();
        let mut deref_binders: BTreeSet<String> = BTreeSet::new();
        for arm in &edge.arms {
            match resolve_arm_binding(arm, &caller_params, &declared_bindings) {
                ArmResolution::Resolved {
                    equation,
                    bindings,
                    deref_names,
                } => {
                    for (binder, ty) in bindings {
                        if ctx.get_variable_type(&binder).is_none() {
                            ctx.declare_var_typed(&binder, ty.clone());
                        }
                        declared_bindings.insert(binder, ty);
                    }
                    arm_equations.push(equation);
                    deref_binders.extend(deref_names);
                }
                ArmResolution::Skip => {}
                ArmResolution::Fail => return TerminationCheck::NotAdmitted,
            }
        }

        // Strip the erased `Box` deref off any recursive-child binder before
        // substitution, so the callee argument `*p` becomes the declared `p`.
        let stripped_args: Vec<syn::Expr> = edge
            .args
            .iter()
            .map(|arg| strip_field_deref(arg, &deref_binders))
            .collect();
        let substitution: HashMap<String, syn::Expr> = callee_info
            .params
            .iter()
            .zip(stripped_args.iter())
            .map(|(param, arg)| (param.name.clone(), arg.clone()))
            .collect();
        let callee_params: HashMap<&str, &TrustVcType> = callee_info
            .params
            .iter()
            .map(|param| (param.name.as_str(), &param.ty))
            .collect();
        // Shape the callee (new) measure the same way, but render the
        // SUBSTITUTED argument under the `dt_size` wrapper when the callee's
        // measure component is a direct recursive-datatype parameter.
        let new_components: Vec<String> = callee_info
            .measures
            .iter()
            .map(|measure| {
                let substituted = substitute_idents(measure, &substitution);
                shape_callee_component(measure, &substituted, &callee_params)
            })
            .collect();
        let new_measure = render_component_tuple(&new_components);

        let decrease = crate::decreases_lex::well_founded_lexicographic_decreases_condition(
            &old_measure,
            &new_measure,
        );
        let body_condition = format!("({decrease}) && ({caller_nonneg})");

        // The antecedent is the conjunction of the `if` path conditions AND the
        // reconstructed constructor equations. Folding the arm equation into the
        // (implication) antecedent — rather than a global assume — keeps mutually
        // exclusive arms (`t == A(x)` vs `t == B(y)`) from contradicting each
        // other and collapsing the whole query to a vacuous pass.
        let mut antecedents: Vec<String> = edge
            .path
            .iter()
            .map(|condition| {
                // The false branch of `if n == 0` is normally rendered as
                // `!(n == 0)`. For a `nat` parameter the encoder also asserts
                // `0 <= n`, so that guard is exactly `0 < n`. Keep the query in
                // that inequality form: AY can attach a checked LIA certificate
                // to the resulting decrease proof, whereas the equivalent
                // disequality currently requires an uncertified generic split.
                // This is a typed equivalence, not a strengthening: non-`nat`
                // guards and every unsupported syntactic shape stay unchanged.
                nat_zero_false_guard_lower_bound(condition, &caller_params)
                    .unwrap_or_else(|| condition.clone())
            })
            .map(|condition| format!("({condition})"))
            .collect();
        antecedents.extend(arm_equations.iter().map(|eq| format!("({eq})")));
        let guarded = if antecedents.is_empty() {
            body_condition
        } else {
            let antecedent = antecedents.join(" && ");
            format!("(!({antecedent})) || ({body_condition})")
        };

        ctx.push_obligation(ProofObligation::assert(
            format!("__termination_{caller}_{index}"),
            guarded,
        ));
    }

    match ctx.verify() {
        VerifyResult::Verified => TerminationCheck::Proven,
        VerifyResult::Counterexample { .. } => TerminationCheck::NotAdmitted,
        inconclusive => TerminationCheck::Inconclusive(inconclusive),
    }
}

/// Whether a block introduces a pattern binding with one of `names`.
///
/// The function parameters themselves are outside `body`, so every matching
/// `PatIdent` here is a genuine shadowing site (including `let`, closure, `for`,
/// and match-arm bindings). The conservative whole-body rejection keeps the
/// string-rendered isolated termination query from confusing two scopes.
fn block_binds_any_name(body: &syn::Block, names: &BTreeSet<&str>) -> bool {
    struct BindingScan<'a> {
        names: &'a BTreeSet<&'a str>,
        found: bool,
    }

    impl<'ast> Visit<'ast> for BindingScan<'_> {
        fn visit_pat_ident(&mut self, pattern: &'ast syn::PatIdent) {
            let ident = pattern.ident.to_string();
            if self.names.iter().any(|name| *name == ident.as_str()) {
                self.found = true;
            }
            syn::visit::visit_pat_ident(self, pattern);
        }
    }

    let mut scan = BindingScan {
        names,
        found: false,
    };
    scan.visit_block(body);
    scan.found
}

/// Re-express `!(n == 0)` / `!(0 == n)` as `0 < n` when `n` is a `nat` caller
/// parameter. Nat declarations carry the global invariant `0 <= n`, making the
/// two predicates equivalent. Returning `None` preserves the original guard.
fn nat_zero_false_guard_lower_bound(
    condition: &str,
    caller_params: &HashMap<&str, &TrustVcType>,
) -> Option<String> {
    fn peel(mut expr: &syn::Expr) -> &syn::Expr {
        loop {
            expr = match expr {
                syn::Expr::Paren(paren) => &paren.expr,
                syn::Expr::Group(group) => &group.expr,
                _ => return expr,
            };
        }
    }

    fn bare_name(expr: &syn::Expr) -> Option<String> {
        let syn::Expr::Path(path) = peel(expr) else {
            return None;
        };
        if path.qself.is_some()
            || path.path.leading_colon.is_some()
            || path.path.segments.len() != 1
        {
            return None;
        }
        path.path
            .segments
            .first()
            .map(|segment| segment.ident.to_string())
    }

    fn is_zero(expr: &syn::Expr) -> bool {
        matches!(
            peel(expr),
            syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Int(value),
                ..
            }) if matches!(value.base10_parse::<u128>(), Ok(0))
        )
    }

    let parsed = syn::parse_str::<syn::Expr>(condition).ok()?;
    let syn::Expr::Unary(negated) = peel(&parsed) else {
        return None;
    };
    if !matches!(negated.op, syn::UnOp::Not(_)) {
        return None;
    }
    let syn::Expr::Binary(equality) = peel(&negated.expr) else {
        return None;
    };
    if !matches!(equality.op, syn::BinOp::Eq(_)) {
        return None;
    }
    let name = if is_zero(&equality.right) {
        bare_name(&equality.left)?
    } else if is_zero(&equality.left) {
        bare_name(&equality.right)?
    } else {
        return None;
    };
    matches!(caller_params.get(name.as_str()), Some(TrustVcType::Nat))
        .then(|| format!("0 < {name}"))
}

/// Renders pre-rendered measure component strings as the scalar (single) or
/// parenthesized tuple (lexicographic) form expected by
/// [`crate::decreases_lex::lexicographic_decreases_condition`].
fn render_component_tuple(parts: &[String]) -> String {
    match parts {
        [single] => single.clone(),
        many => format!("({})", many.join(", ")),
    }
}

/// Renders one caller-side (`old`) measure component. A direct single-identifier
/// reference to a recursive-datatype parameter becomes `__trust_vc_dt_size(n)`;
/// any other component is parenthesized verbatim (so a trailing cast such as
/// `(m - 1) as nat` is not mis-parsed once spliced into a `<` comparison).
fn shape_caller_component(measure: &syn::Expr, params: &HashMap<&str, &TrustVcType>) -> String {
    if let Some(name) = direct_param_ident(measure) {
        if params
            .get(name.as_str())
            .is_some_and(|ty| is_recursive_datatype(ty))
        {
            return format!("__trust_vc_dt_size({name})");
        }
    }
    format!("({})", quote!(#measure))
}

/// Renders one callee-side (`new`) measure component. The `dt_size` decision is
/// taken from the callee's ORIGINAL measure component (a direct recursive-datatype
/// parameter), but the SUBSTITUTED argument expression is what is wrapped/rendered.
fn shape_callee_component(
    original: &syn::Expr,
    substituted: &syn::Expr,
    params: &HashMap<&str, &TrustVcType>,
) -> String {
    if let Some(name) = direct_param_ident(original) {
        if params
            .get(name.as_str())
            .is_some_and(|ty| is_recursive_datatype(ty))
        {
            return format!("__trust_vc_dt_size({})", quote!(#substituted));
        }
    }
    format!("({})", quote!(#substituted))
}

/// The bare identifier a measure component references directly (through parens),
/// or `None` for any compound expression.
fn direct_param_ident(expr: &syn::Expr) -> Option<String> {
    match expr {
        syn::Expr::Paren(paren) => direct_param_ident(&paren.expr),
        syn::Expr::Group(group) => direct_param_ident(&group.expr),
        syn::Expr::Path(path)
            if path.qself.is_none()
                && path.path.leading_colon.is_none()
                && path.path.segments.len() == 1 =>
        {
            path.path
                .segments
                .first()
                .map(|segment| segment.ident.to_string())
        }
        _ => None,
    }
}

/// Whether `ty` is a self-recursive datatype (a variant carries a `RecursiveRef`
/// back to the datatype itself) — exactly the carriers `dt_size` is declared for.
fn is_recursive_datatype(ty: &TrustVcType) -> bool {
    let TrustVcType::Datatype { name, variants } = ty else {
        return false;
    };
    variants.iter().any(|variant| {
        variant.fields.iter().any(
            |(_, field_ty)| matches!(field_ty, TrustVcType::RecursiveRef(target) if target == name),
        )
    })
}

/// Outcome of reconstructing a constructor match-arm into a structural equation.
enum ArmResolution {
    /// `scrutinee == Ctor(binders...)` with the field binders to declare and the
    /// recursive-child binder names whose `*p` deref is transparent.
    Resolved {
        equation: String,
        bindings: Vec<(String, TrustVcType)>,
        deref_names: BTreeSet<String>,
    },
    /// Not a modeled arm (scrutinee is not a recursive-datatype parameter, the
    /// constructor does not resolve, or the arity disagrees): contribute nothing.
    Skip,
    /// A field binder collides with an existing declaration of a different type:
    /// fail closed.
    Fail,
}

/// Reconstructs `scrutinee == Ctor(field_binders...)` from a captured match-arm,
/// resolving each field binder's type from the scrutinee's datatype definition.
/// A recursive child field (`Box<Self>` → `RecursiveRef`) is declared as the
/// owning datatype and recorded for transparent-deref stripping.
fn resolve_arm_binding(
    arm: &ArmBinding,
    caller_params: &HashMap<&str, &TrustVcType>,
    declared: &HashMap<String, TrustVcType>,
) -> ArmResolution {
    // The scrutinee must be a caller parameter of recursive-datatype type.
    let Some(scrutinee_ty) = caller_params.get(arm.scrutinee.as_str()) else {
        return ArmResolution::Skip;
    };
    if !is_recursive_datatype(scrutinee_ty) {
        return ArmResolution::Skip;
    }
    let TrustVcType::Datatype {
        name: dt_name,
        variants,
    } = scrutinee_ty
    else {
        return ArmResolution::Skip;
    };
    let Some(ctor_name) = arm
        .constructor_path
        .segments
        .last()
        .map(|segment| segment.ident.to_string())
    else {
        return ArmResolution::Skip;
    };
    let Some(variant) = variants.iter().find(|variant| variant.name == ctor_name) else {
        return ArmResolution::Skip;
    };
    if variant.fields.len() != arm.field_pats.len() {
        return ArmResolution::Skip;
    }

    let mut field_exprs: Vec<String> = Vec::with_capacity(variant.fields.len());
    let mut bindings: Vec<(String, TrustVcType)> = Vec::new();
    let mut deref_names: BTreeSet<String> = BTreeSet::new();
    for (index, ((_, field_ty), field_pat)) in
        variant.fields.iter().zip(arm.field_pats.iter()).enumerate()
    {
        // A recursive-child field declared `Box<Self>` carries a bare `Self`; declare
        // the binder as the full datatype so its `dt_size` is in scope.
        let (resolved_ty, is_recursive_child) = match field_ty {
            TrustVcType::RecursiveRef(target) if target == dt_name => {
                ((*scrutinee_ty).clone(), true)
            }
            other => (other.clone(), false),
        };
        let binder = match field_pat {
            Some(ident) => {
                if is_recursive_child {
                    deref_names.insert(ident.clone());
                }
                ident.clone()
            }
            None => format!("__trust_vc_arm_{}_{}_{}", arm.scrutinee, ctor_name, index),
        };
        if let Some(existing) = declared.get(&binder) {
            if existing != &resolved_ty {
                return ArmResolution::Fail;
            }
        }
        bindings.push((binder.clone(), resolved_ty));
        field_exprs.push(binder);
    }

    let constructor_path = &arm.constructor_path;
    let constructor = quote!(#constructor_path).to_string();
    let equation = format!(
        "{} == {}({})",
        arm.scrutinee,
        constructor,
        field_exprs.join(", ")
    );
    ArmResolution::Resolved {
        equation,
        bindings,
        deref_names,
    }
}

/// Strips the transparent `Box` deref `*p` down to `p` for any binder in `names`
/// (a recursive child field), descending the whole expression. Other derefs are
/// left untouched (they fail closed in lowering as before).
fn strip_field_deref(expr: &syn::Expr, names: &BTreeSet<String>) -> syn::Expr {
    struct Stripper<'a> {
        names: &'a BTreeSet<String>,
    }
    impl Fold for Stripper<'_> {
        fn fold_expr(&mut self, expr: syn::Expr) -> syn::Expr {
            if let syn::Expr::Unary(unary) = &expr {
                if matches!(unary.op, syn::UnOp::Deref(_)) {
                    if let Some(name) = direct_param_ident(&unary.expr) {
                        if self.names.contains(&name) {
                            return (*unary.expr).clone();
                        }
                    }
                }
            }
            syn::fold::fold_expr(self, expr)
        }
    }
    Stripper { names }.fold_expr(expr.clone())
}

/// Substitutes single-segment identifiers with replacement expressions
/// (callee parameter -> actual argument), descending through the whole tree.
fn substitute_idents(expr: &syn::Expr, map: &HashMap<String, syn::Expr>) -> syn::Expr {
    struct Substituter<'a> {
        map: &'a HashMap<String, syn::Expr>,
    }
    impl Fold for Substituter<'_> {
        fn fold_expr(&mut self, expr: syn::Expr) -> syn::Expr {
            if let syn::Expr::Path(path) = &expr {
                if path.qself.is_none()
                    && path.path.leading_colon.is_none()
                    && path.path.segments.len() == 1
                {
                    if let Some(segment) = path.path.segments.first() {
                        if let Some(replacement) = self.map.get(&segment.ident.to_string()) {
                            return replacement.clone();
                        }
                    }
                }
            }
            syn::fold::fold_expr(self, expr)
        }
    }
    Substituter { map }.fold_expr(expr.clone())
}

/// Extracts the parsed `decreases` measure expression(s) from a function's
/// attributes (the first `#[decreases(...)]`/`#[trust_vc::decreases(...)]`).
fn decreases_measure_exprs(attrs: &[syn::Attribute]) -> Option<Vec<syn::Expr>> {
    for attr in attrs {
        let is_decreases = attr
            .path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "decreases");
        if !is_decreases {
            continue;
        }
        if let syn::Meta::List(list) = &attr.meta {
            if let Ok(exprs) = crate::decreases::parse_measure_exprs(list.tokens.clone()) {
                if !exprs.is_empty() {
                    return Some(exprs);
                }
            }
        }
    }
    None
}

/// Scans a function body for recursive call edges, tracking the path condition
/// (conjunction of enclosing `if` guards) under which each call executes.
///
/// Path conditions only ever UNDER-approximate the true guard (e.g. `match` arms
/// and `&&`/`||` short-circuits keep the enclosing guard rather than refining
/// it). That makes the decrease HARDER to prove — never easier — so the scan is
/// sound (fail-closed): it can over-suppress an exotic recursion but can never
/// admit one whose measure does not actually decrease.
struct RecursiveCallScan<'a> {
    members: &'a BTreeSet<String>,
    path: Vec<String>,
    arms: Vec<ArmBinding>,
    calls: Vec<RecursiveEdge>,
}

impl RecursiveCallScan<'_> {
    /// The bare (single-segment) callee identifier, matching the same edge model
    /// `called_names_in_block` uses to build the SCC.
    fn bare_callee(call: &syn::ExprCall) -> Option<String> {
        let syn::Expr::Path(path) = call.func.as_ref() else {
            return None;
        };
        if path.qself.is_some() || path.path.segments.len() != 1 {
            return None;
        }
        path.path
            .segments
            .first()
            .map(|segment| segment.ident.to_string())
    }

    /// Renders an `if` condition as a guard string, or `None` when it cannot be
    /// used as a boolean path condition (e.g. `if let` patterns).
    fn guard_string(cond: &syn::Expr) -> Option<String> {
        if matches!(cond, syn::Expr::Let(_)) {
            return None;
        }
        Some(quote!(#cond).to_string())
    }

    /// The bare identifier a `match` scrutinizes directly, or `None` for any
    /// compound scrutinee (only a parameter we can name in an equation is usable).
    fn scrutinee_ident(expr: &syn::Expr) -> Option<String> {
        if let syn::Expr::Path(path) = expr {
            if path.qself.is_none()
                && path.path.leading_colon.is_none()
                && path.path.segments.len() == 1
            {
                return path
                    .path
                    .segments
                    .first()
                    .map(|segment| segment.ident.to_string());
            }
        }
        None
    }

    /// Captures a flat tuple-struct constructor pattern `Ctor(f0, f1, ...)` over
    /// `scrutinee` as an [`ArmBinding`]. Field sub-patterns are `Some(ident)` for a
    /// binder and `None` for a wildcard; any nested/struct sub-pattern makes the
    /// arm unmodelable (returns `None` — fail closed).
    fn constructor_arm_binding(scrutinee: &str, pat: &syn::Pat) -> Option<ArmBinding> {
        let syn::Pat::TupleStruct(tuple_struct) = pat else {
            return None;
        };
        let mut field_pats = Vec::with_capacity(tuple_struct.elems.len());
        for elem in &tuple_struct.elems {
            match elem {
                syn::Pat::Ident(pat_ident)
                    if pat_ident.by_ref.is_none() && pat_ident.subpat.is_none() =>
                {
                    field_pats.push(Some(pat_ident.ident.to_string()));
                }
                syn::Pat::Wild(_) => field_pats.push(None),
                // Nested / struct / literal field sub-patterns are not modeled.
                _ => return None,
            }
        }
        Some(ArmBinding {
            scrutinee: scrutinee.to_string(),
            constructor_path: tuple_struct.path.clone(),
            field_pats,
        })
    }
}

impl<'ast> Visit<'ast> for RecursiveCallScan<'_> {
    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if let Some(callee) = Self::bare_callee(call) {
            if self.members.contains(&callee) {
                self.calls.push(RecursiveEdge {
                    callee,
                    args: call.args.iter().cloned().collect(),
                    path: self.path.clone(),
                    arms: self.arms.clone(),
                });
            }
        }
        // Descend into the callee expression and arguments to find recursive
        // calls nested inside argument positions (e.g. `ack(m - 1, ack(m, n - 1))`).
        syn::visit::visit_expr_call(self, call);
    }

    /// A method self-call `recv.m(args)` whose method name is a cycle member is a
    /// recursive edge — the SAME edge model the SCC builder uses (`PathCallCollector`
    /// matches method calls by bare method name). Capturing it keeps this scan
    /// COMPLETE with respect to the SCC: a missed method edge would let a
    /// non-decreasing recursive method falsely prove termination (unsound), so
    /// mirroring the free-call arm here is soundness-critical, not an optimization.
    /// The receiver is NOT an argument — `args` are the value arguments, aligned
    /// with the callee's receiver-excluded [`member_value_params`].
    fn visit_expr_method_call(&mut self, call: &'ast syn::ExprMethodCall) {
        let callee = call.method.to_string();
        if self.members.contains(&callee) {
            self.calls.push(RecursiveEdge {
                callee,
                args: call.args.iter().cloned().collect(),
                path: self.path.clone(),
                arms: self.arms.clone(),
            });
        }
        // Descend into the receiver and arguments for nested recursive calls.
        syn::visit::visit_expr_method_call(self, call);
    }

    fn visit_expr_match(&mut self, match_expr: &'ast syn::ExprMatch) {
        // The scrutinee is evaluated before any arm is selected, so recursive calls
        // inside it run under the enclosing arms only (no new arm binding).
        self.visit_expr(&match_expr.expr);

        let scrutinee = Self::scrutinee_ident(&match_expr.expr);
        for arm in &match_expr.arms {
            // An arm `if`-guard runs once the pattern matches, so the arm's binding
            // is in scope there too; push it before visiting guard and body.
            let binding = scrutinee
                .as_ref()
                .and_then(|name| Self::constructor_arm_binding(name, &arm.pat));
            let pushed = binding.is_some();
            if let Some(binding) = binding {
                self.arms.push(binding);
            }
            if let Some((_, guard)) = &arm.guard {
                self.visit_expr(guard);
            }
            self.visit_expr(&arm.body);
            if pushed {
                self.arms.pop();
            }
        }
    }

    fn visit_expr_if(&mut self, if_expr: &'ast syn::ExprIf) {
        // A recursive call inside the condition itself runs under the enclosing
        // path condition (the condition is always evaluated when control reaches
        // the `if`).
        self.visit_expr(&if_expr.cond);

        let guard = Self::guard_string(&if_expr.cond);
        if let Some(guard) = &guard {
            self.path.push(guard.clone());
        }
        self.visit_block(&if_expr.then_branch);
        if guard.is_some() {
            self.path.pop();
        }

        if let Some((_, else_branch)) = &if_expr.else_branch {
            if let Some(guard) = &guard {
                self.path.push(format!("!({guard})"));
            }
            self.visit_expr(else_branch);
            if guard.is_some() {
                self.path.pop();
            }
        }
    }
}

impl SpecFunctionDef {
    fn from_item_fn(
        item_fn: &syn::ItemFn,
        symbol_name: &str,
        ctx: &VerificationContext,
        recursion_without_full_decreases: bool,
        concrete_carriers: &HashMap<String, TrustVcType>,
    ) -> TrustVcResult<Self> {
        // The SMT symbol / helper name is the CATALOG KEY: a module-qualified
        // `module::f` for a nested spec fn, or the bare ident for a top-level one.
        // The caller's lowered call name equals this key, so the helper declaration,
        // the trigger, the defining-axiom head, and `env.lookup_fn` all agree.
        let name = symbol_name.to_string();
        // The bare ident is how a self-call is spelled inside the body, and is the
        // right (`::`-free) hint for generating fresh bound-variable names.
        let bare_ident = item_fn.sig.ident.to_string();
        let is_opaque = has_opaque_attr(&item_fn.attrs);
        // Propagate inline call-site substitution for inline spec functions,
        // including GENERIC ones. Inline substitution replaces the call with the
        // body under the CONCRETE call-site arguments (Verus's exact inline
        // semantics), so a generic inline fn is reasoned about per call site with
        // no uninterpreted-UF sort to mismatch. This lets a generic tuple-return
        // (`swap<A, B>(a, b) -> (B, A) { (b, a) }`) verify: the substituted body
        // `(b, a)` is renormalized to the concrete tuple carrier `(bool, u8)` by
        // `substitute_inline_calls` (see `substitution_inline.rs`). Generic
        // identity stays verified (its body is the bare value, substituted to the
        // concrete arg). A generic inline fn whose body cannot be lowered
        // (`value.some_trait_method()` on a bare type param) still fails closed —
        // the body axiom simply fails to lower, exactly as before. Part of #2777.
        let is_inline = has_inline_attr(&item_fn.attrs);
        // Verus parity (upstream inline.rs `test_rec_fails1` / `test_rec_fails2`):
        // an `#[inline]` spec function may not be recursive, because its body is
        // substituted at every call site — a self-reference would not terminate.
        // A `decreases` clause DECLARES recursion intent, so `inline` + `decreases`
        // is rejected with "'inline' functions cannot be recursive"; a genuine
        // self-call with NO `decreases` is rejected with "recursive function must
        // have a decreases clause" (Verus's messages, verbatim). Both are
        // fail-closed rejections of the DEFINITION — they surface when a verified
        // function references this inline fn (the catalog is applied lazily per
        // referenced dependency), and are scoped to `is_inline` so ordinary
        // recursive spec fns keep their existing `decreases` termination handling.
        // Rejecting can never wrongly verify.
        if is_inline {
            // Verus parity (upstream inline.rs `test_private_fails`): `#[inline]`
            // on a `closed` spec fn is rejected with
            // "'inline' is only allowed for private or 'open spec' functions".
            // A `closed` spec fn hides its body from callers, but inline
            // substitution needs the body VISIBLE at the call site, so the two are
            // mutually exclusive. In trust-vc, `#[trust_vc::opaque]` is the faithful
            // analog of Verus `closed` (the body is hidden/uninterpreted until
            // `reveal!`), so `inline` + `opaque` reproduces the same rejection with
            // the verbatim message. This is fail-closed (it rejects the DEFINITION)
            // and can never wrongly verify. It also loses no faithful behavior: an
            // opaque body is uninterpreted, so it cannot be inline-substituted in
            // the first place — there is no `inline` + `opaque` spec fn trust-vc
            // could legitimately verify that this excludes.
            if is_opaque {
                return Err(TrustVcError::Encoding {
                    context: "register inline spec function",
                    detail: "'inline' is only allowed for private or 'open spec' functions"
                        .to_string(),
                });
            }
            if has_decreases_attr(&item_fn.attrs) {
                return Err(TrustVcError::Encoding {
                    context: "register inline spec function",
                    detail: "'inline' functions cannot be recursive".to_string(),
                });
            }
            if called_names_in_block(&item_fn.block).contains(&bare_ident) {
                return Err(TrustVcError::Encoding {
                    context: "register inline spec function",
                    detail: "recursive function must have a decreases clause".to_string(),
                });
            }
        }
        let mut params = spec_params(&item_fn.sig, ctx)?;
        let mut return_ty = spec_return_type(&item_fn.sig, ctx)?;

        // Per-instantiation monomorphization of a generic spec fn over a
        // recursive datatype. We infer the spec fn's `TypeParam` bindings by
        // matching each parameter's TEMPLATE carrier (`GList`, with a
        // `TypeParam("T")` field) against the concrete carrier the verified
        // function constructs (`GList<i32>`), then rewrite the parameter and
        // return types to that instantiation. This makes the helper/axiom
        // carrier identical to the value carrier the constructor lowering builds
        // (concrete field sorts, self-only `RecursiveRef`) — exactly how a
        // builtin `List<i32>` already lines up — instead of leaving a template
        // `GList` (whose `TypeParam` field erases to `Poly`) that mismatches the
        // concrete argument sort. Distinct instantiations stay distinct carriers;
        // an instantiation that cannot be inferred simply isn't rewritten (the
        // generic helper stays uninterpreted — sound, just incomplete).
        if !concrete_carriers.is_empty() {
            let mut mono_bindings: Vec<(String, TrustVcType)> = Vec::new();
            for param in &params {
                if let TrustVcType::Datatype { name: carrier, .. } = &param.ty {
                    let base = carrier.split('<').next().unwrap_or(carrier);
                    if let Some(concrete) = concrete_carriers.get(base) {
                        param
                            .ty
                            .collect_type_param_bindings(concrete, &mut mono_bindings);
                    }
                }
            }
            if !mono_bindings.is_empty() {
                for param in &mut params {
                    param.ty = param.ty.monomorphize(&mono_bindings);
                }
                return_ty = return_ty.monomorphize(&mono_bindings);
            }
        }

        if return_ty.contains_opaque() {
            return Err(TrustVcError::Encoding {
                context: "source spec function catalog",
                detail: format!(
                    "spec function '{}' has unsupported return type '{}'",
                    name,
                    return_ty.to_type_string()
                ),
            });
        }
        if let Some(param) = params.iter().find(|param| param.ty.contains_opaque()) {
            return Err(TrustVcError::Encoding {
                context: "source spec function catalog",
                detail: format!(
                    "spec function '{}' has unsupported parameter type '{}' for '{}'",
                    name,
                    param.ty.to_type_string(),
                    param.name
                ),
            });
        }

        let mut used_names: BTreeSet<String> = ctx
            .variables()
            .iter()
            .map(|variable| variable.name.clone())
            .collect();
        let mut rename_map = HashMap::new();
        let mut bound_vars = Vec::with_capacity(params.len());
        for param in &params {
            let fresh = fresh_bound_name(&mut used_names, &bare_ident, &param.name);
            rename_map.insert(param.name.clone(), fresh.clone());
            bound_vars.push(fresh);
        }

        reject_shadowing_param_binders(item_fn, &params)?;
        reject_block_items(item_fn)?;

        // The marker is injected only after this source audit and accepted only
        // by a crate-private obligation capability. Reject authored use (and an
        // authored bare definition with the same identity) before constructing
        // the body axiom, so a user cannot smuggle a privileged coercion into a
        // nested call inside an otherwise-authenticated source-catalog body.
        if bare_ident == SOURCE_CATALOG_MATH_INT_MARKER
            || called_names_in_block(&item_fn.block).contains(SOURCE_CATALOG_MATH_INT_MARKER)
        {
            return Err(TrustVcError::Encoding {
                context: "source spec function catalog",
                detail: format!(
                    "`{SOURCE_CATALOG_MATH_INT_MARKER}` is a reserved internal marker and cannot appear in authored source"
                ),
            });
        }

        let call_args = bound_vars.join(", ");
        let trigger = format!("{}({})", name, call_args);

        // An `uninterp` spec fn has NO body: its block is the empty one
        // `mark_bodyless_spec_fns_uninterp` synthesized, and lowering it would
        // fabricate a definition the source never wrote. `apply_to_context`
        // declares the symbol and emits no axiom at all; the vacuous
        // `f(x) == f(x)` here is a defence-in-depth placeholder that would prove
        // nothing even if it somehow reached the solver.
        let is_uninterp = has_uninterp_attr(&item_fn.attrs);
        let body_condition = if is_uninterp {
            format!("{trigger} == {trigger}")
        } else {
            let mut renamed_block = (*item_fn.block).clone();
            IdentRenamer { rename_map }.visit_block_mut(&mut renamed_block);
            let body = quote!(#renamed_block).to_string();
            // A finite-width value used directly as the result of a Verus
            // `spec fn -> int` is interpreted in the mathematical-integer
            // context of that result. In particular, `fn double(x: u16) ->
            // int { x + x }` denotes the unbounded sum, not `bv2int(bvadd
            // x x)`. Preserve that expected-type context across the
            // source-catalog string seam with a reserved lowering marker. The
            // marker is erased into typed IR by `ir_lowering::dispatch::calls`;
            // it never reaches the solver as an uninterpreted function.
            if matches!(return_ty, TrustVcType::MathInt) {
                format!("{trigger} == {SOURCE_CATALOG_MATH_INT_MARKER}({body})")
            } else {
                format!("{trigger} == {body}")
            }
        };

        // Soundness gate: a recursive spec function's defining axiom is faithful
        // only if the recursion terminates. Verus requires a `decreases` clause on
        // every member of a recursive cycle for exactly this reason. The cycle-level
        // decision (direct self-recursion AND mutual `a -> b -> a` cycles) is
        // computed by the catalog — which alone can see all cycle members — and
        // threaded in here as `recursion_without_full_decreases` (see field doc).

        Ok(Self {
            name,
            params,
            return_ty,
            body_condition,
            trigger,
            bound_vars,
            is_opaque,
            is_uninterp,
            is_inline,
            recursion_without_full_decreases,
        })
    }

    /// Install this spec function's helper declaration and — when its body is
    /// visible — its defining body axiom.
    ///
    /// `is_revealed` is a QUERY-LEVEL `reveal!(f)` (a statement of the verified
    /// function's body). `is_scope_revealed` is a `reveal!(f)` written inside an
    /// `assert … by { .. }` proof BLOCK, which Verus scopes to that block (#34).
    ///
    /// The two are gated differently:
    /// * query-level reveal → the axiom is emitted NOT-opaque, i.e. visible to
    ///   every obligation in the query (pre-existing behavior, byte-identical);
    /// * scope-only reveal → the axiom is emitted but MARKED OPAQUE, so the
    ///   query-level gate in `setup_broadcasts` suppresses it everywhere. It is
    ///   unsuppressed only while verifying the one by-block that revealed it, via
    ///   `PreparedVerificationContext::assert_by_scope_revealed_fns`. Emitting it
    ///   NOT-opaque here would leak the body to every later obligation — the
    ///   cardinal proves-more-than-Verus failure (upstream
    ///   `assert_forall_by.rs::test_assertby1_fail2`).
    /// * neither → no axiom at all (the function stays strictly uninterpreted).
    fn apply_to_context(
        &self,
        ctx: &mut VerificationContext,
        is_revealed: bool,
        is_scope_revealed: bool,
    ) {
        let helper_params = self
            .params
            .iter()
            .map(|param| (param.name.clone(), param.ty.clone()))
            .collect();
        ctx.declare_helper_function_typed(&self.name, self.return_ty.clone(), helper_params);

        // A Verus `uninterp spec fn` has NO body, so there is nothing to define
        // and nothing a `reveal!` could turn on. The symbol is declared (calls to
        // it encode as uninterpreted terms of the right sort) and NO defining
        // axiom is ever emitted — unconditionally, ahead of every reveal gate
        // below. Emitting one would invent a definition the source never wrote,
        // proving more than Verus.
        if self.is_uninterp {
            return;
        }

        if self.is_opaque && !is_revealed && !is_scope_revealed {
            return;
        }
        // True exactly in the new scope-only-reveal case (an opaque fn with no
        // query-level reveal). Everywhere else this is `false`, so the emitted
        // axiom is identical to what it was before #34.
        let scope_gated = self.is_opaque && !is_revealed;

        // Fail closed on ill-formed recursion: leave the function uninterpreted
        // (the helper declaration above stands) rather than asserting an unsound
        // defining axiom for a recursive cycle (self- or mutual) that is not fully
        // termination-guarded by `decreases`. See `recursion_without_full_decreases`
        // field doc. Return BEFORE declaring the axiom's fresh binders: without
        // an emitted axiom they are semantically dead, and a discarded `nat`
        // binder's global non-negativity constraint can needlessly turn a ground
        // counterexample into a quantifier-limited `Unknown`.
        if self.recursion_without_full_decreases {
            return;
        }

        for (bound_name, param) in self.bound_vars.iter().zip(self.params.iter()) {
            if ctx.get_variable_type(bound_name).is_none() {
                ctx.declare_var_typed(bound_name, param.ty.clone());
            }
        }

        let axiom_name = format!("__body_axiom_{}_source_catalog", self.name);
        if ctx
            .obligations()
            .iter()
            .any(|obligation| obligation.name() == axiom_name)
        {
            return;
        }

        let mut body_axiom =
            ProofObligation::broadcast_assume(axiom_name, self.body_condition.clone())
                .with_bound_vars(self.bound_vars.clone())
                .with_trigger_patterns(vec![vec![self.trigger.clone()]])
                .with_inline(self.is_inline)
                .with_opaque(scope_gated);
        if matches!(self.return_ty, TrustVcType::MathInt) {
            body_axiom = body_axiom.with_source_catalog_math_int_context();
        }
        ctx.push_obligation(body_axiom);
        // Reaching this point means the source definition had a body, crossed
        // the visibility gate, and (for a recursive SCC) its isolated decreases
        // query was strictly Verified. Preserve that authority separately from
        // the forgeable diagnostic obligation name for exact ground recursive
        // counterexample recovery.
        ctx.record_source_catalog_admitted_definition(self.name.clone());
    }

    /// Install an exact source-name alias for this canonical function.
    ///
    /// The bridge is valid independently of body visibility: Rust name
    /// resolution says both paths denote the same item. It therefore remains
    /// safe for opaque, bodyless, or recursion-suppressed definitions; in those
    /// cases it equates two otherwise-uninterpreted symbols without exposing a
    /// body. The canonical function itself has already been admitted through
    /// [`SpecFunctionCatalog::apply_spec_by_name`].
    fn apply_alias_to_context(
        &self,
        alias: &str,
        canonical_name: &str,
        ctx: &mut VerificationContext,
    ) -> TrustVcResult<()> {
        let helper_params = self
            .params
            .iter()
            .map(|param| (param.name.clone(), param.ty.clone()))
            .collect::<Vec<_>>();
        let expected = (self.return_ty.clone(), helper_params.clone(), vec![]);
        let axiom_name = format!("__alias_axiom_{alias}_to_{canonical_name}_source_catalog");
        if let Some(existing) = ctx.helper_functions_typed.get(alias) {
            let same_exact_alias = ctx
                .obligations()
                .iter()
                .any(|obligation| obligation.name() == axiom_name);
            if existing != &expected || !same_exact_alias {
                return Err(TrustVcError::Encoding {
                    context: "source spec function alias",
                    detail: format!(
                        "alias `{alias}` conflicts with an existing source helper identity; \
                         TrustVc fails closed instead of rebinding the same solver symbol"
                    ),
                });
            }
            return Ok(());
        }
        ctx.declare_helper_function_typed(alias, self.return_ty.clone(), helper_params);

        for (bound_name, param) in self.bound_vars.iter().zip(self.params.iter()) {
            if ctx.get_variable_type(bound_name).is_none() {
                ctx.declare_var_typed(bound_name, param.ty.clone());
            }
        }

        let call_args = self.bound_vars.join(", ");
        let alias_call = format!("{alias}({call_args})");
        let canonical_call = format!("{canonical_name}({call_args})");
        if ctx
            .obligations()
            .iter()
            .any(|obligation| obligation.name() == axiom_name)
        {
            return Ok(());
        }
        ctx.push_obligation(
            ProofObligation::broadcast_assume(
                axiom_name,
                format!("{alias_call} == {canonical_call}"),
            )
            .with_bound_vars(self.bound_vars.clone())
            .with_trigger_patterns(vec![vec![alias_call]]),
        );
        Ok(())
    }
}

/// `reveal!` targets found in a function body, split by SCOPE (#34).
#[derive(Clone, Default)]
struct RevealNames {
    /// `reveal!(f)` as a statement of the function body: Verus makes `f`'s body
    /// visible from that point on, and trust-vc models it query-granularly.
    top_level: BTreeSet<String>,
    /// `reveal!(f)` inside an `assert … by { .. }` proof block: Verus scopes it
    /// to the block. Kept separate so the body axiom is emitted OPAQUE and only
    /// the owning by-block unsuppresses it.
    scoped: BTreeSet<String>,
}

fn revealed_names_in_block(block: &syn::Block) -> RevealNames {
    let mut visitor = RevealNameVisitor::default();
    visitor.visit_block(block);
    visitor.names
}

/// The proof block of an `assert … by { .. }` macro, if `mac` is one.
///
/// `syn::visit` does NOT descend into macro token streams, so without this a
/// `reveal!(f)` inside a by-block is invisible to [`RevealNameVisitor`].
/// Covers `assert_by!(cond, { .. })` and both spellings of the quantified form
/// (`assert_forall_by!(..)` and `assert!(forall |x| .. by { .. })`), i.e. exactly
/// the by-blocks `body_extract` lowers into an `assert_by_scopes` entry with a
/// parseable `syn::Block`. Other proof blocks (`calc!`,
/// `assert_by_contradiction!`) are not matched, so a `reveal!` inside them keeps
/// failing closed (the axiom is never emitted).
pub(crate) fn by_block_proof_block(mac: &syn::Macro) -> Option<syn::Block> {
    let name = mac.path.segments.last()?.ident.to_string();
    match name.as_str() {
        "assert_by" | "trust_vc_assert_by" => match crate::parse_assert_by(mac.tokens.clone()) {
            crate::AssertByParsed::WithProofBlock { proof_block, .. } => {
                syn::parse2::<syn::Block>(proof_block).ok()
            }
            crate::AssertByParsed::Single { .. } => None,
        },
        "assert" | "trust_vc_assert" | "assert_forall_by" => {
            crate::parse_assert_forall_by(mac.tokens.clone())
                .ok()
                .map(|parsed| parsed.proof_block)
        }
        _ => None,
    }
}

#[derive(Default)]
struct RevealNameVisitor {
    names: RevealNames,
    /// Depth of enclosing by-block proof blocks; > 0 means a `reveal!` found
    /// here is SCOPED to that block, not query-level.
    proof_block_depth: usize,
}

impl<'ast> Visit<'ast> for RevealNameVisitor {
    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        if mac
            .path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "reveal")
        {
            if let Ok(path) = syn::parse2::<syn::Path>(mac.tokens.clone()) {
                if let Some(name) = reveal_target_name(&path) {
                    if self.proof_block_depth > 0 {
                        self.names.scoped.insert(name);
                    } else {
                        self.names.top_level.insert(name);
                    }
                }
            }
        }

        if let Some(proof_block) = by_block_proof_block(mac) {
            self.proof_block_depth += 1;
            self.visit_block(&proof_block);
            self.proof_block_depth -= 1;
        }

        syn::visit::visit_macro(self, mac);
    }
}

fn reveal_target_name(path: &syn::Path) -> Option<String> {
    if path.leading_colon.is_some() || path.segments.len() != 1 {
        return None;
    }
    let segment = path.segments.first()?;
    match &segment.arguments {
        syn::PathArguments::None | syn::PathArguments::AngleBracketed(_) => {
            Some(segment.ident.to_string())
        }
        syn::PathArguments::Parenthesized(_) => None,
    }
}

fn spec_params(sig: &syn::Signature, ctx: &VerificationContext) -> TrustVcResult<Vec<SpecParam>> {
    sig.inputs
        .iter()
        .map(|arg| match arg {
            syn::FnArg::Typed(pat_type) => {
                let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
                    return Err(TrustVcError::Encoding {
                        context: "source spec function catalog",
                        detail: format!(
                            "spec function '{}' uses an unsupported parameter pattern",
                            sig.ident
                        ),
                    });
                };
                let ty = source_type_from_context(ctx, &pat_type.ty);
                Ok(SpecParam {
                    name: pat_ident.ident.to_string(),
                    ty,
                })
            }
            syn::FnArg::Receiver(_) => Err(TrustVcError::Encoding {
                context: "source spec function catalog",
                detail: format!("spec function '{}' must not take self", sig.ident),
            }),
        })
        .collect()
}

/// Like [`spec_params`] but SKIPS a leading `self` receiver, so an inherent /
/// trait method's VALUE parameters — the ones a value-parameter `decreases`
/// measure ranges over — are modeled for the Stage-2 termination proof. The
/// receiver is intentionally not a param: it does not appear in a value-parameter
/// measure, and a `self`-referencing measure fails the decrease query closed
/// (undeclared variable). Used only by [`MemberTermInfo::from_source_fn`].
fn member_value_params(
    sig: &syn::Signature,
    ctx: &VerificationContext,
) -> TrustVcResult<Vec<SpecParam>> {
    let mut params = Vec::new();
    for arg in &sig.inputs {
        let syn::FnArg::Typed(pat_type) = arg else {
            continue; // skip the receiver
        };
        let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
            return Err(TrustVcError::Encoding {
                context: "source spec function catalog",
                detail: format!(
                    "spec function '{}' uses an unsupported parameter pattern",
                    sig.ident
                ),
            });
        };
        let ty = source_type_from_context(ctx, &pat_type.ty);
        params.push(SpecParam {
            name: pat_ident.ident.to_string(),
            ty,
        });
    }
    Ok(params)
}

fn spec_return_type(sig: &syn::Signature, ctx: &VerificationContext) -> TrustVcResult<TrustVcType> {
    match &sig.output {
        syn::ReturnType::Type(_, ty) => Ok(source_type_from_context(ctx, ty)),
        syn::ReturnType::Default => Err(TrustVcError::Encoding {
            context: "source spec function catalog",
            detail: format!("spec function '{}' has no return type", sig.ident),
        }),
    }
}

fn source_type_from_context(ctx: &VerificationContext, ty: &syn::Type) -> TrustVcType {
    let ty_str = extract_type_string(ty);
    let base = ctx
        .source_type_aliases()
        .get(&ty_str)
        .cloned()
        .unwrap_or_else(|| TrustVcType::parse_or_opaque(&ty_str));
    // Registry-aware resolution: the flat string parser leaves any user-defined
    // struct/enum that appears as a leaf (including nested inside a container,
    // e.g. the `PbTerm` in `Vec<PbTerm>` -> `Seq(Opaque("PbTerm"))`) as an
    // `Opaque` placeholder, which then trips the `contains_opaque` reject below.
    // Replace each such leaf with the SAME `Datatype` carrier the source struct
    // registry already registered into the context (enums via
    // `register_type_aliases`, structs via `register_struct_type`), so a spec fn
    // can take a `Vec<PbTerm>` / `&[PbTerm]` / `&PbConstraint` parameter or a
    // `Result<i128, ObjectiveEvalError>` return exactly as the verified function
    // body resolves them — the body<->spec carrier identity congruence requires.
    resolve_opaque_leaves(base, ctx)
}

/// Replaces every `Opaque(name)` leaf in `ty` whose `name` is a user struct or
/// enum registered in `ctx` with that type's registered `Datatype` carrier,
/// recursing structurally through containers and datatype fields. Leaves an
/// `Opaque` whose name is genuinely unknown untouched (so it still fails closed).
fn resolve_opaque_leaves(ty: TrustVcType, ctx: &VerificationContext) -> TrustVcType {
    match ty {
        TrustVcType::Opaque(name) => {
            if let Some(alias) = ctx.source_type_aliases().get(&name) {
                return alias.clone();
            }
            if let Some(def) = ctx.struct_types.iter().find(|def| def.name == name) {
                return def.to_datatype_type();
            }
            TrustVcType::Opaque(name)
        }
        TrustVcType::Seq(inner) => TrustVcType::Seq(Box::new(resolve_opaque_leaves(*inner, ctx))),
        TrustVcType::Array(inner, len) => {
            TrustVcType::Array(Box::new(resolve_opaque_leaves(*inner, ctx)), len)
        }
        TrustVcType::Set(inner) => TrustVcType::Set(Box::new(resolve_opaque_leaves(*inner, ctx))),
        TrustVcType::Multiset(inner) => {
            TrustVcType::Multiset(Box::new(resolve_opaque_leaves(*inner, ctx)))
        }
        TrustVcType::Map(key, value) => TrustVcType::Map(
            Box::new(resolve_opaque_leaves(*key, ctx)),
            Box::new(resolve_opaque_leaves(*value, ctx)),
        ),
        TrustVcType::SpecFn(args, ret) => TrustVcType::SpecFn(
            args.into_iter()
                .map(|arg| resolve_opaque_leaves(arg, ctx))
                .collect(),
            Box::new(resolve_opaque_leaves(*ret, ctx)),
        ),
        TrustVcType::Datatype { name, variants } => TrustVcType::Datatype {
            name,
            variants: variants
                .into_iter()
                .map(|variant| {
                    crate::ir::DatatypeVariant::new(
                        variant.name.clone(),
                        variant
                            .fields
                            .into_iter()
                            .map(|(field, field_ty)| (field, resolve_opaque_leaves(field_ty, ctx)))
                            .collect(),
                    )
                })
                .collect(),
        },
        other => other,
    }
}

fn fresh_bound_name(used_names: &mut BTreeSet<String>, fn_name: &str, param_name: &str) -> String {
    let base = format!("__trust_vc_spec_{}_{}", fn_name, param_name);
    if used_names.insert(base.clone()) {
        return base;
    }

    for i in 1.. {
        let candidate = format!("{base}_{i}");
        if used_names.insert(candidate.clone()) {
            return candidate;
        }
    }
    unreachable!("unbounded suffix search must find a fresh name")
}

// ===========================================================================
// Cross-file spec import resolution (same-crate).
// ===========================================================================

/// A crate-wide index of `#[trust_vc::spec]` functions, built by walking the
/// crate module tree once. Used to resolve cross-file `use` imports.
struct CrateSpecIndex {
    /// `(module_path, fn_name)` -> the spec function's `ItemFn`.
    by_path: HashMap<(Vec<String>, String), syn::ItemFn>,
    /// `module_path` -> `[(fn_name, ItemFn)]`, for glob (`use ...::*`) imports.
    by_module: HashMap<Vec<String>, Vec<(String, syn::ItemFn)>>,
}

// Thread-local cache keyed by crate-root path so the crate source walk runs at
// most once per crate per thread even though the catalog is rebuilt for every
// verified function. A thread-local (with `Rc`) rather than a `static` is
// required because `syn::ItemFn` is neither `Send` nor `Sync`; this also keeps
// the cache correct under the parallel verification bridge (each thread builds
// its own). Source files do not change during a verification run, so this is
// safe.
thread_local! {
    static CRATE_SPEC_INDEX_CACHE: RefCell<HashMap<PathBuf, Rc<CrateSpecIndex>>> =
        RefCell::new(HashMap::new());
}

fn get_or_build_crate_spec_index(crate_root: &Path) -> Option<Rc<CrateSpecIndex>> {
    CRATE_SPEC_INDEX_CACHE.with(|cache| {
        if let Some(index) = cache.borrow().get(crate_root) {
            return Some(Rc::clone(index));
        }
        let index = Rc::new(build_crate_spec_index(crate_root)?);
        cache
            .borrow_mut()
            .insert(crate_root.to_path_buf(), Rc::clone(&index));
        Some(index)
    })
}

fn build_crate_spec_index(crate_root: &Path) -> Option<CrateSpecIndex> {
    let mut by_path: HashMap<(Vec<String>, String), syn::ItemFn> = HashMap::new();
    let mut by_module: HashMap<Vec<String>, Vec<(String, syn::ItemFn)>> = HashMap::new();
    crate::source_tree::walk_crate_modules(crate_root, &mut |module_items| {
        for item in module_items.items {
            if let syn::Item::Fn(item_fn) = item {
                if has_spec_attr(&item_fn.attrs) {
                    let module = module_items.module_path.to_vec();
                    let name = item_fn.sig.ident.to_string();
                    by_path.insert((module.clone(), name.clone()), item_fn.clone());
                    by_module
                        .entry(module)
                        .or_default()
                        .push((name, item_fn.clone()));
                }
            }
        }
    })?;
    Some(CrateSpecIndex { by_path, by_module })
}

/// A crate-relative `use` import resolved to its target module + leaf.
struct ResolvedImport {
    /// The name the item is bound to in the importing scope.
    in_scope_name: String,
    /// Crate-relative module path of the target.
    module: Vec<String>,
    /// Leaf item name; `None` denotes a glob (`*`) of the whole module.
    leaf: Option<String>,
}

#[derive(Default)]
struct SpecImportCollector {
    current_module: Vec<String>,
    imports: Vec<ResolvedImport>,
}

impl SpecImportCollector {
    fn collect_tree(&mut self, prefix: &mut Vec<String>, tree: &syn::UseTree) {
        match tree {
            syn::UseTree::Path(path) => {
                prefix.push(path.ident.to_string());
                self.collect_tree(prefix, &path.tree);
                prefix.pop();
            }
            syn::UseTree::Name(name) => {
                let leaf = name.ident.to_string();
                if let Some(module) = resolve_crate_relative_module(prefix, &self.current_module) {
                    self.imports.push(ResolvedImport {
                        in_scope_name: leaf.clone(),
                        module,
                        leaf: Some(leaf),
                    });
                }
            }
            syn::UseTree::Rename(rename) => {
                let leaf = rename.ident.to_string();
                if let Some(module) = resolve_crate_relative_module(prefix, &self.current_module) {
                    self.imports.push(ResolvedImport {
                        in_scope_name: rename.rename.to_string(),
                        module,
                        leaf: Some(leaf),
                    });
                }
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    self.collect_tree(prefix, item);
                }
            }
            syn::UseTree::Glob(_) => {
                if let Some(module) = resolve_crate_relative_module(prefix, &self.current_module) {
                    self.imports.push(ResolvedImport {
                        in_scope_name: String::new(),
                        module,
                        leaf: None,
                    });
                }
            }
        }
    }
}

/// Resolves the module-path portion of a `use` (the segments BEFORE the leaf /
/// glob) to a crate-relative module path. Only `crate`/`self`/`super`-rooted
/// paths resolve; any other first segment (an external crate name, or a bare
/// 2018-edition path) returns `None` so the import is left unresolved (fail
/// closed). Returns `None` if a `super` chain climbs above the crate root.
fn resolve_crate_relative_module(
    segments: &[String],
    current_module: &[String],
) -> Option<Vec<String>> {
    let first = segments.first()?;
    let mut result: Vec<String>;
    let mut idx: usize;
    match first.as_str() {
        "crate" => {
            result = Vec::new();
            idx = 1;
        }
        "self" => {
            result = current_module.to_vec();
            idx = 1;
        }
        "super" => {
            result = current_module.to_vec();
            idx = 0;
            while segments.get(idx).map(String::as_str) == Some("super") {
                result.pop()?;
                idx += 1;
            }
        }
        _ => return None,
    }
    for seg in &segments[idx..] {
        match seg.as_str() {
            // A path qualifier appearing past the head is malformed for our use.
            "crate" | "self" | "super" => return None,
            other => result.push(other.to_string()),
        }
    }
    Some(result)
}

/// Determines a source file's module path relative to the crate root, e.g.
/// `src/specs/helpers.rs` with root `src/lib.rs` -> `["specs", "helpers"]`.
/// Mirrors `recursion_graph::determine_module_path`.
fn current_module_path(source_file: &Path, crate_root: &Path) -> Vec<String> {
    let source_canonical = source_file
        .canonicalize()
        .unwrap_or_else(|_| source_file.to_path_buf());
    let root_canonical = crate_root
        .canonicalize()
        .unwrap_or_else(|_| crate_root.to_path_buf());
    if source_canonical == root_canonical {
        return Vec::new();
    }
    let Some(root_dir) = root_canonical.parent() else {
        return Vec::new();
    };
    let Ok(relative) = source_canonical.strip_prefix(root_dir) else {
        return Vec::new();
    };
    let mut segments: Vec<String> = relative
        .components()
        .filter_map(|component| {
            if let std::path::Component::Normal(s) = component {
                s.to_str().map(|s| s.to_string())
            } else {
                None
            }
        })
        .collect();
    if let Some(last) = segments.last_mut() {
        if let Some(stripped) = last.strip_suffix(".rs") {
            *last = stripped.to_string();
        }
    }
    if segments.last().is_some_and(|s| s == "mod") {
        segments.pop();
    }
    segments
}

pub(crate) fn has_spec_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "spec")
    })
}

/// Recursively collect `pub` `#[trust_vc::spec]` functions nested inside inline
/// modules as `(bare_ident, module-qualified-key, item_fn)`. Top-level functions
/// (empty prefix) are registered separately by the caller and skipped here; a
/// non-`pub` nested fn is skipped so it stays encapsulated (Verus closed-visibility
/// parity).
fn collect_nested_pub_spec_fns(
    prefix: &[String],
    items: &[syn::Item],
    out: &mut Vec<(String, String, syn::ItemFn)>,
) {
    for item in items {
        match item {
            syn::Item::Mod(module) => {
                if let Some((_, inner)) = &module.content {
                    let mut nested_prefix = prefix.to_vec();
                    nested_prefix.push(module.ident.to_string());
                    collect_nested_pub_spec_fns(&nested_prefix, inner, out);
                }
            }
            syn::Item::Fn(item_fn)
                if !prefix.is_empty()
                    && has_spec_attr(&item_fn.attrs)
                    && matches!(item_fn.vis, syn::Visibility::Public(_)) =>
            {
                let ident = item_fn.sig.ident.to_string();
                let qualified_key = format!("{}::{}", prefix.join("::"), ident);
                out.push((ident, qualified_key, item_fn.clone()));
            }
            _ => {}
        }
    }
}

/// Verus `uninterp spec fn f(x: int) -> bool;` — a spec function DECLARED with no
/// body. `tracked_syntax::mark_bodyless_spec_fns_uninterp` stamps this marker on
/// every bodyless spec fn, which is the only way "has no body" survives into an
/// `ItemFn` (whose block is synthesized and empty).
pub(crate) fn has_uninterp_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "uninterp")
    })
}

fn has_opaque_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "opaque")
    })
}

pub(crate) fn has_inline_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "inline")
    })
}

/// Whether the function carries a `#[trust_vc::decreases(...)]` (or bare
/// `#[decreases(...)]`) termination measure. Gates admission of recursive
/// defining axioms — see [`SpecFunctionDef::self_recursive_without_decreases`].
fn has_decreases_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "decreases")
    })
}

fn recommends_conditions(attrs: &[syn::Attribute]) -> Vec<String> {
    attrs
        .iter()
        .filter(|attr| {
            attr.path()
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "recommends")
        })
        .filter_map(|attr| match &attr.meta {
            syn::Meta::List(meta_list) => {
                let condition = meta_list.tokens.to_string();
                (!condition.trim().is_empty()).then_some(condition)
            }
            _ => None,
        })
        .collect()
}

fn is_contract_attr(attr: &syn::Attribute) -> bool {
    attr.path().segments.last().is_some_and(|segment| {
        segment.ident == "requires"
            || segment.ident == "ensures"
            || segment.ident == "recommends"
            || segment.ident == "contract"
    })
}

fn referenced_contract_call_names(func: &syn::ItemFn) -> BTreeSet<String> {
    let mut collector = ContractCallCollector::default();
    for attr in &func.attrs {
        if !is_contract_attr(attr) {
            continue;
        }
        let attr_name = attr
            .path()
            .segments
            .last()
            .map(|segment| segment.ident.to_string());
        if attr_name.as_deref() == Some("contract") {
            if let Ok(clauses) = attr
                .parse_args_with(
                    syn::punctuated::Punctuated::<ContractClause, syn::Token![,]>::parse_terminated,
                )
                .map(|clauses| clauses.into_iter().collect::<Vec<_>>())
            {
                for clause in clauses {
                    for expr in clause.args {
                        collector.visit_expr(&expr);
                    }
                }
            }
        } else if let Ok(expr) = attr.parse_args::<syn::Expr>() {
            collector.visit_expr(&expr);
        } else if let syn::Meta::List(list) = &attr.meta {
            // A clause that is not plain Rust (`==>`/`<==>`, chained
            // comparisons, `|||` bullets) fails the plain parse above; fall
            // back to the chain-aware parser so spec-fn calls inside such
            // clauses still register. Best-effort like the plain path — the
            // authoritative clause parse (and its errors) lives in
            // attr_extract.
            if let Ok(expr) =
                crate::chained_comparisons::parse_expr_tokens_with_chains(list.tokens.clone())
            {
                collector.visit_expr(&expr);
            }
        }
    }
    collector.names
}

struct ContractClause {
    args: Vec<syn::Expr>,
}

impl syn::parse::Parse for ContractClause {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let _name: syn::Ident = input.parse()?;
        let content;
        syn::parenthesized!(content in input);
        let args =
            syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated(&content)?;
        Ok(Self {
            args: args.into_iter().collect(),
        })
    }
}

pub(crate) fn called_names_in_block(block: &syn::Block) -> BTreeSet<String> {
    let mut collector = ContractCallCollector::default();
    collector.visit_block(block);
    collector.names
}

#[derive(Default)]
struct ContractCallCollector {
    names: BTreeSet<String>,
}

impl<'ast> Visit<'ast> for ContractCallCollector {
    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if let syn::Expr::Path(path) = &*call.func {
            if path.qself.is_none() {
                if path.path.segments.len() == 1 {
                    if let Some(segment) = path.path.segments.last() {
                        self.names.insert(segment.ident.to_string());
                    }
                } else {
                    // Multi-segment qualified call (`module::f`): collect the
                    // `::`-joined name so a caller referencing a module-nested spec fn
                    // resolves against the module-qualified catalog key. This equals
                    // `path_to_string` (the lowered call name), keeping the collected
                    // name, the catalog key, and `env.lookup_fn` byte-congruent.
                    let qualified = path
                        .path
                        .segments
                        .iter()
                        .map(|segment| segment.ident.to_string())
                        .collect::<Vec<_>>()
                        .join("::");
                    if !qualified.is_empty() {
                        self.names.insert(qualified);
                    }
                }
            }
        }
        syn::visit::visit_expr_call(self, call);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        // Connective marker macros produced by the chain-aware parser
        // (`__trust_vc_implies!(P, Q)` from `==>`/`<==`, `__trust_vc_iff!(P, Q)`
        // from `<==>`) carry their operands as RAW token sub-streams separated
        // by a top-level comma — not a parseable expression list. Parse each
        // operand separately (chain-aware, so nested connectives normalize the
        // same way) so a spec-fn call inside an implication operand still
        // registers its return type / body axiom. Without this,
        // `assert!(x == y ==> f(x, y) == f(y, x))` (upstream basic.rs test2)
        // missed `f` here and the obligation lowering failed with
        // "unknown return type for function 'f'".
        let marker_name = mac.path.segments.last().map(|s| s.ident.to_string());
        if matches!(
            marker_name.as_deref(),
            Some(crate::chained_comparisons::IMPLIES_MARKER_MACRO)
                | Some(crate::chained_comparisons::IFF_MARKER_MACRO)
        ) {
            for operand in
                crate::chained_comparisons::split_top_level_comma_operands(mac.tokens.clone())
            {
                if let Ok(expr) = crate::chained_comparisons::parse_expr_tokens_with_chains(operand)
                {
                    self.visit_expr(&expr);
                }
            }
            return;
        }

        if is_solver_mode_assert_macro(mac) {
            if let Ok(parsed) = crate::parse_solver_mode_assert(mac.tokens.clone()) {
                self.visit_expr(&parsed.condition);
                for requires in &parsed.requires {
                    self.visit_expr(requires);
                }
            }
            return;
        }

        if is_assert_forall_by_macro(mac) {
            if let Ok(parsed) = crate::parse_assert_forall_by(mac.tokens.clone()) {
                self.visit_expr(&parsed.closure.body);
                for trigger_group in &parsed.trigger_patterns {
                    for trigger in trigger_group {
                        self.visit_expr(trigger);
                    }
                }
                self.visit_block(&parsed.proof_block);
                return;
            }
        }

        // `assert_by!(condition, { proof_block })` (#34): the token stream is
        // `expr , { block }`, which the plain-expression fallback below cannot
        // parse — so every spec fn called from the condition or the proof block
        // would go unregistered and lowering the obligation would fail with
        // "unknown return type for function '…'". Visit both positions.
        if mac.path.segments.last().is_some_and(|segment| {
            segment.ident == "assert_by" || segment.ident == "trust_vc_assert_by"
        }) {
            if let crate::AssertByParsed::WithProofBlock {
                condition,
                proof_block,
            } = crate::parse_assert_by(mac.tokens.clone())
            {
                if let Ok(expr) =
                    crate::chained_comparisons::parse_expr_tokens_with_chains(condition)
                {
                    self.visit_expr(&expr);
                }
                if let Ok(block) = syn::parse2::<syn::Block>(proof_block) {
                    self.visit_block(&block);
                }
                return;
            }
        }

        // Prefer a plain parse; fall back to the chain-aware parser so
        // SOURCE-STYLE quantifier/choose bodies inside a `trust_vc::assert!` /
        // `assume!` token stream are seen. `assert!((choose|n: nat| cnatf(n)) >= 0)`
        // does NOT parse as plain Rust (the bare `choose|n|` reads as a bitwise-or),
        // so the closure body — and the `cnatf` spec-fn call it references — was
        // silently missed here, leaving `cnatf`'s body axiom / return-type
        // registration absent and lowering the obligation failed with "unknown
        // return type for function 'cnatf'". The `choose!(..)` MACRO form parses
        // fine, which is why it worked. Purely additive: only reaches the fallback
        // when the plain parse fails (a previously-skipped token stream).
        let parsed = syn::parse2::<syn::Expr>(mac.tokens.clone()).or_else(|_| {
            crate::chained_comparisons::parse_expr_tokens_with_chains(mac.tokens.clone())
        });
        if let Ok(expr) = parsed {
            self.visit_expr(&expr);
        }
    }
}

fn is_solver_mode_assert_macro(mac: &syn::Macro) -> bool {
    mac.path.segments.last().is_some_and(|segment| {
        segment.ident == "assert_by_nonlinear"
            || segment.ident == "assert_by_bit_vector"
            || segment.ident == "assert_by_compute"
    })
}

fn is_assert_forall_by_macro(mac: &syn::Macro) -> bool {
    mac.path.segments.last().is_some_and(|segment| {
        segment.ident == "assert_forall_by"
            || segment.ident == "assert"
            || segment.ident == "trust_vc_assert"
    })
}

fn reject_shadowing_param_binders(
    item_fn: &syn::ItemFn,
    params: &[SpecParam],
) -> TrustVcResult<()> {
    let param_names = params
        .iter()
        .map(|param| param.name.as_str())
        .collect::<BTreeSet<_>>();
    let mut collector = ParamShadowCollector {
        param_names,
        shadowed: BTreeSet::new(),
    };
    collector.visit_block(&item_fn.block);
    if collector.shadowed.is_empty() {
        return Ok(());
    }
    Err(TrustVcError::Encoding {
        context: "source spec function catalog",
        detail: format!(
            "spec function '{}' shadows parameter(s) {}; source catalog refuses scope-unsafe alpha-renaming",
            item_fn.sig.ident,
            collector
                .shadowed
                .into_iter()
                .collect::<Vec<_>>()
                .join(", ")
        ),
    })
}

fn reject_block_items(item_fn: &syn::ItemFn) -> TrustVcResult<()> {
    if item_fn
        .block
        .stmts
        .iter()
        .any(|stmt| matches!(stmt, syn::Stmt::Item(_)))
    {
        return Err(TrustVcError::Encoding {
            context: "source spec function catalog",
            detail: format!(
                "spec function '{}' contains nested items, which source catalog alpha-renaming does not support",
                item_fn.sig.ident
            ),
        });
    }
    Ok(())
}

struct ParamShadowCollector<'a> {
    param_names: BTreeSet<&'a str>,
    shadowed: BTreeSet<String>,
}

impl<'ast> Visit<'ast> for ParamShadowCollector<'_> {
    fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
        let name = pat.ident.to_string();
        if self.param_names.contains(name.as_str()) {
            self.shadowed.insert(name);
        }
        syn::visit::visit_pat_ident(self, pat);
    }
}

struct IdentRenamer {
    rename_map: HashMap<String, String>,
}

impl VisitMut for IdentRenamer {
    fn visit_expr_path_mut(&mut self, path: &mut syn::ExprPath) {
        if path.qself.is_none() && path.path.segments.len() == 1 {
            let segment = &mut path.path.segments[0];
            if let Some(replacement) = self.rename_map.get(&segment.ident.to_string()) {
                segment.ident = syn::Ident::new(replacement, Span::call_site());
            }
        }
        syn::visit_mut::visit_expr_path_mut(self, path);
    }
}

/// Result of [`SpecFunctionCatalog::collect_concrete_enum_carriers`]: the
/// per-instantiation monomorphization map plus the self-recursive bases the
/// verified function builds at conflicting (>= 2 distinct) instantiations.
struct ConcreteCarrierAnalysis {
    carriers: HashMap<String, TrustVcType>,
    conflicting_recursive_bases: BTreeSet<String>,
}

/// syn visitor that records concrete per-instantiation datatype carriers from
/// enum-variant constructor calls (see
/// [`SpecFunctionCatalog::collect_concrete_enum_carriers`]).
struct ConcreteCarrierCollector<'a> {
    ctx: &'a VerificationContext,
    out: &'a mut HashMap<String, TrustVcType>,
    conflicting: &'a mut BTreeSet<String>,
    /// When `Some` (the verified-function pass only), records the base name of
    /// every SELF-RECURSIVE generic carrier the visited block constructs. The
    /// caller intersects this with `conflicting` to decide whether the function
    /// itself emits a malformed multi-instantiation query that must fail closed
    /// (see `collect_concrete_enum_carriers`). Left `None` for sibling spec-fn
    /// bodies so their constructions never widen the function's fail-close set.
    recursive_bases: Option<&'a mut BTreeSet<String>>,
}

impl<'ast> Visit<'ast> for ConcreteCarrierCollector<'_> {
    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if let Some((base, carrier)) = infer_constructor_carrier(call, self.ctx) {
            if let Some(recursive_bases) = self.recursive_bases.as_deref_mut() {
                if is_recursive_datatype(&carrier) {
                    recursive_bases.insert(base.clone());
                }
            }
            match self.out.get(&base) {
                Some(existing) if existing != &carrier => {
                    // Two distinct instantiations of the same generic enum in
                    // scope (`GList<i32>` and `GList<bool>`). They are genuinely
                    // distinct carriers; we cannot pick one for a single generic
                    // helper symbol, so we drop the base entirely and the generic
                    // spec fn stays uninterpreted (sound, just incomplete).
                    self.conflicting.insert(base);
                }
                Some(_) => {}
                None => {
                    self.out.insert(base, carrier);
                }
            }
        }
        syn::visit::visit_expr_call(self, call);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        // Constructor calls almost always live inside `trust_vc::assert!` /
        // `assume!` macros, whose contents are an unparsed token stream the
        // default `Visit` walk never descends into. Parse the tokens as an
        // expression (mirroring `ContractCallCollector::visit_macro`) so nested
        // constructor calls are seen.
        if let Ok(expr) = syn::parse2::<syn::Expr>(mac.tokens.clone()) {
            self.visit_expr(&expr);
        }
        syn::visit::visit_macro(self, mac);
    }
}

/// Infers the concrete per-instantiation carrier built by an enum-variant
/// constructor call. Returns `(enum_base_name, concrete_carrier)`, e.g.
/// `("GList", GList<i32>)` for `GList::GCons(5i32, ..)`. Returns `None` unless
/// every `TypeParam` of the matched template carrier is pinned to a concrete
/// type by the call's arguments.
fn infer_constructor_carrier(
    call: &syn::ExprCall,
    ctx: &VerificationContext,
) -> Option<(String, TrustVcType)> {
    let syn::Expr::Path(expr_path) = &*call.func else {
        return None;
    };
    if expr_path.qself.is_some() {
        return None;
    }
    let segments: Vec<String> = expr_path
        .path
        .segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect();
    let variant_name = segments.last()?.clone();
    let (base, template) = resolve_template_carrier(&segments, &variant_name, ctx)?;
    let TrustVcType::Datatype { variants, .. } = &template else {
        return None;
    };
    let variant = variants.iter().find(|v| v.name == variant_name)?;
    if variant.fields.len() != call.args.len() {
        return None;
    }
    let mut bindings: Vec<(String, TrustVcType)> = Vec::new();
    for ((_, field_ty), arg) in variant.fields.iter().zip(call.args.iter()) {
        if let Some(arg_ty) = infer_syn_arg_type(arg, ctx) {
            field_ty.collect_type_param_bindings(&arg_ty, &mut bindings);
        }
    }
    if bindings.is_empty() {
        return None;
    }
    let carrier = template.monomorphize(&bindings);
    if type_contains_type_param(&carrier) {
        return None;
    }
    Some((base, carrier))
}

/// Resolves the template carrier (and its base name) for a constructor path.
/// A qualified path (`GList::GCons`) uses the penultimate segment as the enum
/// hint; an unqualified variant (`GCons`) is resolved only when exactly one
/// registered enum carrier defines a variant with that name.
fn resolve_template_carrier(
    segments: &[String],
    variant_name: &str,
    ctx: &VerificationContext,
) -> Option<(String, TrustVcType)> {
    let carrier_base = |carrier: &TrustVcType| -> Option<String> {
        match carrier {
            TrustVcType::Datatype { name, .. } => {
                Some(name.split('<').next().unwrap_or(name).to_string())
            }
            _ => None,
        }
    };
    if segments.len() >= 2 {
        let hint = &segments[segments.len() - 2];
        let carrier = ctx.source_type_aliases().get(hint)?;
        let base = carrier_base(carrier)?;
        return Some((base, carrier.clone()));
    }
    // Unqualified: find the unique enum carrier defining this variant.
    let mut found: Option<(String, TrustVcType)> = None;
    for carrier in ctx.source_type_aliases().values() {
        let TrustVcType::Datatype { variants, .. } = carrier else {
            continue;
        };
        if variants.iter().any(|v| v.name == variant_name) {
            let base = carrier_base(carrier)?;
            match &found {
                Some((existing_base, _)) if existing_base != &base => return None,
                Some(_) => {}
                None => found = Some((base, carrier.clone())),
            }
        }
    }
    found
}

/// Best-effort syntactic type inference of a constructor argument expression,
/// sufficient to pin a generic recursive datatype's type arguments. Handles
/// suffixed integer / bool literals, in-scope variables, `Box`/`Rc`/`Arc::new`
/// wrappers, and (recursively) nested enum-variant constructor calls.
fn infer_syn_arg_type(expr: &syn::Expr, ctx: &VerificationContext) -> Option<TrustVcType> {
    match expr {
        syn::Expr::Reference(reference) => infer_syn_arg_type(&reference.expr, ctx),
        syn::Expr::Paren(paren) => infer_syn_arg_type(&paren.expr, ctx),
        syn::Expr::Group(group) => infer_syn_arg_type(&group.expr, ctx),
        syn::Expr::Lit(lit) => match &lit.lit {
            syn::Lit::Int(int) => TrustVcType::try_from_str(int.suffix()).ok(),
            syn::Lit::Bool(_) => Some(TrustVcType::Bool),
            _ => None,
        },
        syn::Expr::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => {
            let ident = path.path.segments[0].ident.to_string();
            ctx.get_variable_type(&ident).cloned()
        }
        syn::Expr::Call(call) => {
            if let syn::Expr::Path(func_path) = &*call.func {
                let tail: Vec<String> = func_path
                    .path
                    .segments
                    .iter()
                    .rev()
                    .take(2)
                    .map(|s| s.ident.to_string())
                    .collect();
                // `Box::new(x)` / `Rc::new(x)` / `Arc::new(x)` are transparent
                // smart-pointer wrappers at the SMT level: infer the payload.
                if tail.first().is_some_and(|s| s == "new")
                    && tail
                        .get(1)
                        .is_some_and(|s| s == "Box" || s == "Rc" || s == "Arc")
                {
                    return call
                        .args
                        .first()
                        .and_then(|inner| infer_syn_arg_type(inner, ctx));
                }
            }
            infer_constructor_carrier(call, ctx).map(|(_, carrier)| carrier)
        }
        _ => None,
    }
}

/// True if `ty` is or contains an unresolved `TypeParam`.
fn type_contains_type_param(ty: &TrustVcType) -> bool {
    match ty {
        TrustVcType::TypeParam(_) => true,
        TrustVcType::Seq(inner)
        | TrustVcType::Array(inner, _)
        | TrustVcType::Set(inner)
        | TrustVcType::Multiset(inner) => type_contains_type_param(inner),
        TrustVcType::Map(key, value) => {
            type_contains_type_param(key) || type_contains_type_param(value)
        }
        TrustVcType::SpecFn(args, ret) => {
            args.iter().any(type_contains_type_param) || type_contains_type_param(ret)
        }
        TrustVcType::Datatype { variants, .. } => variants.iter().any(|variant| {
            variant
                .fields
                .iter()
                .any(|(_, ft)| type_contains_type_param(ft))
        }),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalizes_only_nat_zero_false_guards_to_positive_bounds() {
        let nat = TrustVcType::Nat;
        let math_int = TrustVcType::MathInt;
        let nat_params = HashMap::from([("n", &nat)]);
        let int_params = HashMap::from([("n", &math_int)]);

        assert_eq!(
            nat_zero_false_guard_lower_bound("!(n == 0)", &nat_params).as_deref(),
            Some("0 < n")
        );
        assert_eq!(
            nat_zero_false_guard_lower_bound("!((0 == n))", &nat_params).as_deref(),
            Some("0 < n")
        );
        assert_eq!(
            nat_zero_false_guard_lower_bound("!(n == 0)", &int_params),
            None,
            "an unbounded integer may be negative, so disequality is not positivity"
        );
        assert_eq!(
            nat_zero_false_guard_lower_bound("!(n == 1)", &nat_params),
            None
        );
        assert_eq!(
            nat_zero_false_guard_lower_bound("n == 0", &nat_params),
            None
        );
    }

    #[test]
    fn detects_parameter_shadowing_across_pattern_binding_forms() {
        let names = BTreeSet::from(["n"]);
        let clean: syn::Block = syn::parse_quote!({
            let other = n;
            if n == 0 {
                0
            } else {
                other
            }
        });
        let shadowed_let: syn::Block = syn::parse_quote!({
            let n = 7;
            n
        });
        let shadowed_closure: syn::Block = syn::parse_quote!({
            let f = |n| n + 1;
            f(n)
        });

        assert!(!block_binds_any_name(&clean, &names));
        assert!(block_binds_any_name(&shadowed_let, &names));
        assert!(block_binds_any_name(&shadowed_closure, &names));
    }

    #[test]
    fn normalizes_open_spec_named_return() {
        let source = "pub open spec fn double(x: u16) -> (z: int) { x + x }";
        let normalized = normalize_open_spec_source(source);
        assert!(normalized.contains("#[trust_vc::spec]"));
        assert!(normalized.contains("pub fn double"));
        assert!(normalized.contains("-> int"));
        syn::parse_file(&normalized).expect("normalized open spec should parse as Rust");
    }
}
