//! Builder and mutation methods for VerificationContext.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from `context/mod.rs` for the 500-line limit (#2621).

use super::{DemandInlineConfig, FunctionContext, VariableDecl, VerificationContext};
use crate::counterexample_names::CounterexampleVarMeta;
use crate::ir::{StructDef, TraitDecl, TraitImplDecl};
use crate::solver_budget::ConflictBudget;
use crate::vc::obligation::{InvariantMask, ObligationKind, ProofObligation, SolverMode};

impl VerificationContext {
    fn assert_assert_by_scope_name_fresh(&self, name: &str) {
        assert!(
            !self.assert_by_scopes.contains_key(name) && !self.forall_bound_vars.contains_key(name),
            "invariant: duplicate assert_by scope name `{name}`"
        );
    }

    /// Adds an `assert ... by { ... }` obligation with a scoped proof block.
    pub fn add_assert_by(
        &mut self,
        name: &str,
        condition: &str,
        scoped_obligations: Vec<ProofObligation>,
    ) {
        self.add_assert_by_with_solver_mode(name, condition, scoped_obligations, None);
    }

    /// Adds an `assert ... by` obligation with an optional solver mode.
    pub fn add_assert_by_with_solver_mode(
        &mut self,
        name: &str,
        condition: &str,
        scoped_obligations: Vec<ProofObligation>,
        solver_mode: Option<SolverMode>,
    ) {
        let name = name.to_owned();
        let condition = condition.to_owned();
        self.assert_assert_by_scope_name_fresh(&name);
        let scoped_obligations = scoped_obligations
            .into_iter()
            .map(|obligation| match solver_mode {
                Some(mode) if obligation.kind == ObligationKind::Requires => {
                    obligation.with_solver_mode(mode)
                }
                _ => obligation,
            })
            .collect();
        self.assert_by_scopes
            .insert(name.clone(), scoped_obligations);
        let mut obligation = ProofObligation::assert_by(name, condition);
        if let Some(mode) = solver_mode {
            obligation = obligation.with_solver_mode(mode);
        }
        self.obligations.push(obligation);
    }

    /// Associates a loop guard condition with the named invariant.
    pub fn add_loop_guard(&mut self, invariant_name: &str, guard_condition: &str) {
        self.loop_guards
            .insert(invariant_name.to_owned(), guard_condition.to_owned());
    }

    /// Records which variables are modified by the loop identified by `invariant_name`.
    pub fn set_loop_modified_vars(&mut self, invariant_name: &str, vars: Vec<String>) {
        self.loop_modified_vars
            .insert(invariant_name.to_owned(), vars);
    }

    /// Records the straight-line loop-body transition for the named invariant.
    ///
    /// Each entry maps a loop-modified variable to the scoped-value string
    /// giving its post-body value expressed over loop-head (pre-state)
    /// variables. The frame-condition inductive step uses these to bind the
    /// havoc'd current-state variable to its single-iteration transition.
    /// Part of M4 loop-body transition.
    pub fn set_loop_body_transition(
        &mut self,
        invariant_name: &str,
        transitions: Vec<(String, String)>,
    ) {
        self.loop_body_transitions
            .insert(invariant_name.to_owned(), transitions);
    }

    /// Registers the ENTRY assumptions (loop-modified let-local pre-loop values)
    /// scoped to the named loop invariant's BASE-CASE (entry) check only.
    pub fn set_loop_entry_scope(
        &mut self,
        invariant_name: &str,
        entry_obligations: Vec<ProofObligation>,
    ) {
        self.loop_entry_scopes
            .insert(invariant_name.to_owned(), entry_obligations);
    }

    /// Registers a helper function by name and return type string (deprecated).
    #[deprecated(since = "0.1.0", note = "use declare_helper_function_typed")]
    pub fn declare_helper_function(&mut self, name: &str, return_type: &str) {
        self.helper_functions
            .insert(name.to_owned(), return_type.to_owned());
    }

    /// Register a helper function with fully-typed signature. Supports
    /// TypeParam return types that `declare_helper_function` (string-based)
    /// cannot parse. Part of #2431.
    pub fn declare_helper_function_typed(
        &mut self,
        name: &str,
        return_type: crate::ir::TrustVcType,
        params: Vec<(String, crate::ir::TrustVcType)>,
    ) {
        self.helper_functions_typed
            .insert(name.to_owned(), (return_type, params, vec![]));
    }

    /// Register inherent-impl method metadata so that `recv.method(args)` in a
    /// specification context lowers to a typed `FnCall` (`uf_name` applied to the
    /// receiver and arguments). Keyed by `(self_type_string, method_name)`; the
    /// metadata is threaded into `TypeEnv` by `prepare_context`'s
    /// `build_type_env`. The definitional body axiom (if any) is registered
    /// separately as a broadcast-assume obligation. Part of A3.
    pub(crate) fn register_inherent_method(
        &mut self,
        self_type: String,
        method_name: String,
        uf_name: String,
        return_type: crate::ir::TrustVcType,
        param_types: Vec<crate::ir::TrustVcType>,
    ) {
        self.inherent_methods.insert(
            (self_type, method_name),
            (uf_name, return_type, param_types),
        );
    }

    /// Records how an impl method (inherent OR trait) takes its `self` receiver,
    /// keyed by `(base_self_type_name, method_name)`. Drives the user-struct
    /// receiver-mutation detection (the analog of the #62/#63 collection
    /// loop-mutation gap). On a key collision with DIFFERENT kinds (the same
    /// `(type, method)` declared `&self` in one impl and `&mut self` in another —
    /// e.g. an inherent method and a trait method sharing a name), fail closed by
    /// promoting to the most-mutating kind (`RefMut`) so a possible mutation is
    /// never missed.
    pub(crate) fn register_struct_self_receiver_kind(
        &mut self,
        self_type: String,
        method_name: String,
        kind: crate::vc::context::SelfReceiverKind,
    ) {
        use crate::vc::context::SelfReceiverKind;
        self.struct_self_receiver_kinds
            .entry((self_type, method_name))
            .and_modify(|existing| {
                if *existing != kind {
                    *existing = SelfReceiverKind::RefMut;
                }
            })
            .or_insert(kind);
    }

    /// Records how a TRAIT-DECLARED method takes its `self` receiver, keyed by
    /// `(declaring_trait_name, method_name)`. Drives the GENERIC-receiver
    /// mutation detection (a `TypeParam`-typed receiver has no `Datatype`, so
    /// `register_struct_self_receiver_kind` can never classify it). Same
    /// fail-closed collision rule: on a conflicting re-registration, promote to
    /// the most-mutating kind so a possible mutation is never missed.
    pub(crate) fn register_trait_method_self_receiver_kind(
        &mut self,
        trait_name: String,
        method_name: String,
        kind: crate::vc::context::SelfReceiverKind,
    ) {
        use crate::vc::context::SelfReceiverKind;
        self.trait_method_self_receiver_kinds
            .entry((trait_name, method_name))
            .and_modify(|existing| {
                if *existing != kind {
                    *existing = SelfReceiverKind::RefMut;
                }
            })
            .or_insert(kind);
    }

    /// Register a helper function with trait bounds so they survive
    /// `prepare_context()` and reach `setup_from_prepared`. Part of #2425.
    pub fn declare_helper_function_typed_with_bounds(
        &mut self,
        name: &str,
        return_type: crate::ir::TrustVcType,
        params: Vec<(String, crate::ir::TrustVcType)>,
        trait_bounds: Vec<crate::ir::TraitBound>,
    ) {
        self.helper_functions_typed
            .insert(name.to_owned(), (return_type, params, trait_bounds));
    }

    /// Registers a trait declaration, deduplicating by equality.
    pub fn register_trait_decl(&mut self, decl: TraitDecl) {
        if !self.trait_decls.contains(&decl) {
            self.trait_decls.push(decl);
        }
    }

    /// Registers a trait implementation declaration, deduplicating by equality.
    ///
    /// SHADOW-SET UNION, and it is soundness-critical. Two producers reach this
    /// method for the same impl: the file lane
    /// (`trait_contracts::collect_source_trait_declarations`, which computes
    /// `inherent_shadowed_methods` against the whole file) and the thread-local
    /// catalog lane (`trait_registry::apply_registered_traits_to_context`, whose
    /// `TraitCatalog` may have been built from a different scope). Plain
    /// equality-dedup would treat a shadowed decl and an unshadowed one as
    /// DIFFERENT and keep BOTH — and the encoder iterates every decl, so the
    /// unshadowed copy would emit the very linking axiom the shadowed one
    /// declines to emit, silently defeating the gate.
    ///
    /// Shadowing only ever SUPPRESSES an axiom about a symbol the file resolves
    /// to another declaration, so the UNION is the fail-closed merge: if ANY
    /// producer determined the symbol is contested, it stays contested.
    pub fn register_trait_impl(&mut self, decl: TraitImplDecl) {
        if let Some(existing) = self
            .trait_impl_decls
            .iter_mut()
            .find(|existing| existing.matches_ignoring_shadowed_methods(&decl))
        {
            existing
                .inherent_shadowed_methods
                .extend(decl.inherent_shadowed_methods);
            return;
        }
        self.trait_impl_decls.push(decl);
    }

    /// Records the captured single-pure-return body of a trait-impl method,
    /// keyed by its declaring TRAIT plus its concrete UF name. Consumed only by
    /// the auxiliary trait-conformance pass to assume the impl method's
    /// definitional fact while checking it against the trait contract.
    ///
    /// The key used to be the bare concrete UF name, with a doc comment claiming
    /// "the source declaration is unique per concrete name". It is not: the
    /// concrete name carries the self type but NOT the trait, so `impl A1 for S`
    /// and `impl A2 for S` both mint `S__v` and this first-wins insert handed
    /// A1's body to A2's conformance obligation — every trait after the first
    /// counterexampled against a foreign body. See [`crate::ir::ImplMethodKey`].
    /// First registration still wins, but the key is now genuinely unique, so
    /// nothing but a literal duplicate declaration can reach that branch.
    pub fn register_trait_impl_method_body(
        &mut self,
        key: crate::ir::ImplMethodKey,
        body: crate::ir::ConformanceMethodBody,
    ) {
        self.trait_impl_method_bodies.entry(key).or_insert(body);
    }

    /// Records a trait-impl method's OWN declared `ensures` postconditions,
    /// keyed by its declaring TRAIT plus its concrete UF name (see
    /// [`Self::register_trait_impl_method_body`] for why the trait is
    /// load-bearing). Only called for a non-exempt impl method whose body was
    /// ALSO captured, so the conformance pass can verify `body ⊨ impl_ensures`
    /// before the strengthened postcondition is propagated to callers.
    pub fn register_trait_impl_method_ensures(
        &mut self,
        key: crate::ir::ImplMethodKey,
        ensures: Vec<String>,
    ) {
        self.trait_impl_method_ensures.entry(key).or_insert(ensures);
    }

    /// Marks a trait-impl method (by its concrete UF name) as exempt from the
    /// auxiliary conformance pass because it is BLOCKED by a dedicated
    /// ill-formedness error (own `requires`, or a `returns`-on-both conflict).
    /// The blocked impl is still rejected via that error when verified directly;
    /// the exemption only prevents it from sinking unrelated functions.
    pub fn register_conformance_exempt_method(&mut self, concrete_fn_name: String) {
        self.conformance_exempt_methods.insert(concrete_fn_name);
    }

    /// Register a user-defined struct type for verification. Part of #2419.
    pub fn register_struct_type(&mut self, def: StructDef) {
        if !self.struct_types.iter().any(|s| s.name == def.name) {
            self.struct_types.push(def);
        }
    }

    /// Attach a type invariant to a registered struct type. Part of #2419.
    pub fn set_type_invariant(&mut self, type_name: &str, invariant: crate::ir::TrustVcExpr) {
        assert!(
            self.struct_types.iter().any(|def| def.name == type_name),
            "invariant: cannot register type invariant for unknown struct type `{type_name}`"
        );
        self.type_invariants.insert(type_name.to_owned(), invariant);
    }

    /// Set the invariant mask for this function's verification context.
    /// Controls which invariant namespaces may be opened. Part of #2427.
    pub fn set_invariant_mask(&mut self, mask: InvariantMask) {
        self.invariant_mask = mask;
    }

    /// Override the per-function WALL-CLOCK backstop, in milliseconds.
    ///
    /// This moves the LIVENESS bound only. It does not change how much work
    /// the solver is allowed to do — that is
    /// [`Self::set_rlimit_conflicts`], the deterministic budget — so a
    /// verdict obtained by raising this number alone is still a
    /// machine-dependent verdict. Part of #2489.
    pub fn set_rlimit(&mut self, ms: u64) {
        self.rlimit_ms = Some(ms);
    }

    /// Override the per-function DETERMINISTIC work budget, in SAT conflicts.
    ///
    /// Unlike [`Self::set_rlimit`], this bound is machine-independent: the
    /// same query stops at the same conflict count on every host under every
    /// load. Exhausting it yields `Unknown` (`resourceout`), never
    /// `Verified`.
    pub fn set_rlimit_conflicts(&mut self, budget: ConflictBudget) {
        self.rlimit_conflicts = Some(budget);
    }

    /// Skip the timeout retry cascade (int-mode + extended-timeout stages).
    /// When enabled, assertions that timeout on the initial BV attempt return
    /// Unknown immediately instead of attempting two additional encoder setups.
    /// Saves ~30s per timeout assertion. Part of #2707.
    pub fn set_skip_retry_cascade(&mut self, skip: bool) {
        self.skip_retry_cascade = skip;
    }

    /// Set the full demand-inline retry config. Part of #2655.
    pub fn set_demand_inline_config(&mut self, config: DemandInlineConfig) {
        self.demand_inline = config;
    }

    /// Enable or disable demand-inline retry. Part of #2655.
    pub fn set_demand_inline_enabled(&mut self, enabled: bool) {
        self.demand_inline = self.demand_inline.with_enabled(enabled);
    }

    /// Set the maximum body-expansion depth for demand-inline retry. Part of #2655.
    pub fn set_demand_inline_depth(&mut self, depth_bound: usize) {
        self.demand_inline = self.demand_inline.with_depth_bound(depth_bound);
    }

    /// Set the maximum number of retry-selected callees. Part of #2655.
    pub fn set_demand_inline_max_callees(&mut self, max_callees: usize) {
        self.demand_inline = self.demand_inline.with_max_callees(max_callees);
    }

    /// Register an explicit counterexample display alias for a variable.
    ///
    /// Overrides the default naming policy from `counterexample_names::default_meta`.
    /// Use at helper-generation sites (old! captures, closure params, mut-ref SSA)
    /// to provide user-facing names. Part of #2651.
    pub fn register_counterexample_alias(
        &mut self,
        raw_name: impl Into<String>,
        display_name: impl Into<String>,
        visible: bool,
    ) {
        self.counterexample_var_meta.insert(
            raw_name.into(),
            CounterexampleVarMeta {
                display_name: display_name.into(),
                visible,
            },
        );
    }

    /// Returns whether a variable with the given name has been declared.
    #[must_use]
    pub fn has_variable(&self, name: &str) -> bool {
        self.variable_index.contains_key(name)
    }

    /// Looks up the type of a declared variable by name.
    pub fn get_variable_type(&self, name: &str) -> Option<&crate::ir::TrustVcType> {
        let idx = *self.variable_index.get(name)?;
        self.variables.get(idx).map(|variable| &variable.ty)
    }

    /// Marks a declared variable as an erased immutable reference.
    pub fn mark_erased_shared_ref_var(&mut self, name: &str) {
        if self.variable_index.contains_key(name) {
            self.erased_shared_ref_vars.insert(name.to_owned());
        }
    }

    /// Returns whether a variable was declared from an erased immutable reference.
    #[must_use]
    pub fn is_erased_shared_ref_var(&self, name: &str) -> bool {
        self.erased_shared_ref_vars.contains(name)
    }

    /// Marks a declared variable as an erased `Ghost<T>` wrapper.
    pub fn mark_erased_ghost_var(&mut self, name: &str) {
        if self.variable_index.contains_key(name) {
            self.erased_ghost_vars.insert(name.to_owned());
        }
    }

    /// Returns whether a variable was declared from an erased `Ghost<T>` wrapper.
    #[must_use]
    pub fn is_erased_ghost_var(&self, name: &str) -> bool {
        self.erased_ghost_vars.contains(name)
    }

    /// Registers a prophecy variable binding with its symbolic inner type.
    pub fn register_prophecy_binding(&mut self, name: &str, ty: crate::ir::TrustVcType) {
        self.prophecy_bindings.insert(name.to_owned(), ty);
    }

    /// Returns the prophecy bindings map (name to symbolic inner type).
    pub fn prophecy_bindings(&self) -> &std::collections::HashMap<String, crate::ir::TrustVcType> {
        &self.prophecy_bindings
    }

    /// Registers a source-local type alias with its resolved TrustVc type.
    pub fn register_source_type_alias(&mut self, name: &str, ty: crate::ir::TrustVcType) {
        self.source_type_aliases.insert(name.to_owned(), ty);
    }

    /// Returns source-local type aliases (alias name to resolved TrustVc type).
    pub fn source_type_aliases(
        &self,
    ) -> &std::collections::HashMap<String, crate::ir::TrustVcType> {
        &self.source_type_aliases
    }

    /// Declares a variable from a parsed TrustVc type string.
    ///
    /// This keeps examples/tests concise while routing through the typed
    /// declaration path used by production callers.
    pub fn declare_var_parsed(&mut self, name: &str, ty: &str) {
        let trust_vc_ty = crate::ir::TrustVcType::parse_or_opaque(ty);
        self.declare_var_typed(name, trust_vc_ty);
    }

    /// Declares a variable by parsing a type string (deprecated).
    #[deprecated(since = "0.1.0", note = "use declare_var_typed")]
    pub fn declare_var(&mut self, name: &str, ty: &str) {
        self.declare_var_parsed(name, ty);
    }

    /// Detects a collision between a user variable and the `{name}_dom` domain
    /// companion the encoder mints for every `Map` variable (#1966).
    ///
    /// SOUNDNESS/DETECTION-CRITICAL, and it must live HERE rather than at the
    /// minting site. Three independent reasons:
    ///
    /// 1. **The encoder may never run.** Variable declaration is not eager:
    ///    `verify` prunes to the obligations' reachable variables, and a context
    ///    whose only obligation is trivially true declares nothing at all. A
    ///    check at the minting site is therefore silently skippable, which is
    ///    exactly how this collision became undetectable.
    /// 2. **The solver cannot be delegated to.** `try_declare_const` rejects a
    ///    redeclaration only when the SORTS DIFFER. A user variable
    ///    `x_dom: Map<K, bool>` lowers to precisely the domain sort
    ///    `Array(K, Bool)`, so ay accepts it as an idempotent redeclaration and
    ///    the user's variable is silently conflated with `x`'s domain array.
    /// 3. **`{name}_dom` is the only companion minted into the USER namespace.**
    ///    The length companion (`__trust_vc_len_*`) and the native-seq shadow
    ///    (`__trust_vc_native_seq_shadow_*`) both sit behind a reserved prefix
    ///    and are unreachable by a legal Rust identifier; `{name}_dom` is not.
    ///
    /// Both declaration orders are rejected, because the encoder mints the
    /// companion lazily and the user variable may be declared on either side of
    /// the `Map`. The collision is an embedder mistake, so this fails CLOSED
    /// with a `VerifyResult::Error` rather than picking a winner.
    fn map_domain_companion_conflict(
        &self,
        name: &str,
        ty: &crate::ir::TrustVcType,
    ) -> Option<String> {
        // Order A: the `Map` is declared second — its companion name is already
        // taken by a previously declared user variable.
        if matches!(ty, crate::ir::TrustVcType::Map(_, _)) {
            let dom_name = format!("{name}_dom");
            if self.variable_index.contains_key(&dom_name) {
                return Some(format!(
                    "Variable '{dom_name}' is already declared and collides with the \
                     map domain companion minted for map '{name}'"
                ));
            }
        }
        // Order B: the `Map` is declared first — a later user variable lands on
        // the companion name. Only a `Map` base can mint one, so a plain
        // `foo_dom` alongside a non-`Map` `foo` stays legal.
        if let Some(base) = name.strip_suffix("_dom") {
            if self
                .variable_index
                .get(base)
                .and_then(|idx| self.variables.get(*idx))
                .is_some_and(|decl| matches!(decl.ty, crate::ir::TrustVcType::Map(_, _)))
            {
                return Some(format!(
                    "Variable '{name}' collides with the map domain companion minted \
                     for map '{base}', which is already declared"
                ));
            }
        }
        None
    }

    /// Declares a variable with a fully-typed TrustVc type.
    ///
    /// The declared variable's length is left UNBOUNDED (spec-`Seq` default). Use
    /// `Self::declare_var_typed_bounded` for an exec `Vec`/slice/array whose
    /// length is `usize`-bounded.
    pub fn declare_var_typed(&mut self, name: &str, ty: crate::ir::TrustVcType) {
        self.declare_var_typed_bounded(name, ty, false);
    }

    /// Declares a variable, recording whether its origin syn type is a
    /// `usize`-bounded exec collection (`Vec`/slice/array). See
    /// [`VariableDecl::bounded_len`] for the soundness contract — `bounded_len`
    /// MUST be `false` for a spec `Seq<T>`.
    pub(crate) fn declare_var_typed_bounded(
        &mut self,
        name: &str,
        ty: crate::ir::TrustVcType,
        bounded_len: bool,
    ) {
        if self.variable_index.contains_key(name) {
            self.duplicate_var_error = Some(format!("Variable '{}' already declared", name));
            return;
        }
        if let Some(conflict) = self.map_domain_companion_conflict(name, &ty) {
            self.duplicate_var_error = Some(conflict);
            return;
        }
        let idx = self.variables.len();
        self.variables.push(VariableDecl {
            name: name.to_owned(),
            ty,
            bounded_len,
        });
        self.variable_index.insert(name.to_owned(), idx);
    }

    #[cfg(test)]
    pub(crate) fn push_variable(&mut self, decl: VariableDecl) {
        let idx = self.variables.len();
        self.variable_index.insert(decl.name.clone(), idx);
        self.variables.push(decl);
    }

    /// Declares a named constant with a known value.
    ///
    /// Equivalent to `declare_var(name, ty)` + `add_assume(name_value, "name == value")`.
    /// Used for global/static specifications where a constant's value is an axiom.
    /// Part of #2423.
    #[deprecated(since = "0.1.0", note = "use declare_const_typed")]
    pub fn declare_const(&mut self, name: &str, ty: &str, value: &str) {
        self.declare_var_typed(name, crate::ir::TrustVcType::parse_or_opaque(ty));
        self.push_obligation(ProofObligation::assume(
            format!("{}_value", name),
            format!("{} == {}", name, value),
        ));
    }

    /// Typed variant of `declare_const`. Part of #2423.
    pub fn declare_const_typed(&mut self, name: &str, ty: crate::ir::TrustVcType, value: &str) {
        self.declare_var_typed(name, ty);
        self.push_obligation(ProofObligation::assume(
            format!("{}_value", name),
            format!("{} == {}", name, value),
        ));
    }

    /// Adds an `assert forall ... by { ... }` obligation.
    ///
    /// Proves a universally quantified property using a proof block that has
    /// the bound variables in scope. Bound variables are scoped to the
    /// corresponding `AssertBy` proof and reintroduced as a quantified fact
    /// once the proof succeeds. Part of #2416, #2551.
    #[deprecated(since = "0.1.0", note = "use add_assert_forall_by_typed")]
    pub fn add_assert_forall_by(
        &mut self,
        name: &str,
        body: &str,
        bound_vars: Vec<(&str, &str)>,
        proof_block: Vec<ProofObligation>,
    ) {
        let name = name.to_owned();
        self.assert_assert_by_scope_name_fresh(&name);
        let decls: Vec<VariableDecl> = bound_vars
            .iter()
            .map(|(vname, vtype)| VariableDecl {
                bounded_len: false,
                name: vname.to_string(),
                ty: crate::ir::TrustVcType::parse_or_opaque(vtype),
            })
            .collect();
        let bound_var_names = decls.iter().map(|decl| decl.name.clone()).collect();
        self.forall_bound_vars.insert(name.clone(), decls);
        self.assert_by_scopes.insert(name.clone(), proof_block);
        self.obligations
            .push(ProofObligation::assert_by(name, body).with_bound_vars(bound_var_names));
    }

    /// Typed variant of `add_assert_forall_by`. Part of #2416.
    pub fn add_assert_forall_by_typed(
        &mut self,
        name: &str,
        body: &str,
        bound_vars: Vec<(&str, crate::ir::TrustVcType)>,
        proof_block: Vec<ProofObligation>,
    ) {
        self.add_assert_forall_by_typed_with_trigger_patterns(
            name,
            body,
            bound_vars,
            proof_block,
            Vec::new(),
        );
    }

    /// Typed variant of `add_assert_forall_by` with explicit trigger patterns.
    pub fn add_assert_forall_by_typed_with_trigger_patterns(
        &mut self,
        name: &str,
        body: &str,
        bound_vars: Vec<(&str, crate::ir::TrustVcType)>,
        proof_block: Vec<ProofObligation>,
        trigger_patterns: Vec<Vec<String>>,
    ) {
        let name = name.to_owned();
        self.assert_assert_by_scope_name_fresh(&name);
        let decls: Vec<VariableDecl> = bound_vars
            .into_iter()
            .map(|(vname, vtype)| VariableDecl {
                bounded_len: false,
                name: vname.to_string(),
                ty: vtype,
            })
            .collect();
        let bound_var_names = decls.iter().map(|decl| decl.name.clone()).collect();
        self.forall_bound_vars.insert(name.clone(), decls);
        self.assert_by_scopes.insert(name.clone(), proof_block);
        let mut obligation =
            ProofObligation::assert_by(name, body).with_bound_vars(bound_var_names);
        if !trigger_patterns.is_empty() {
            obligation = obligation.with_trigger_patterns(trigger_patterns);
        }
        self.obligations.push(obligation);
    }

    /// Pushes a measure-decreases obligation with an optional source location.
    pub fn add_measure_decreases_obligation(
        &mut self,
        name: &str,
        condition: &str,
        location: Option<String>,
    ) {
        let mut obligation = ProofObligation::measure_decreases(name, condition);
        if let Some(loc) = location {
            obligation = obligation.with_location(loc);
        }
        self.obligations.push(obligation);
    }

    /// Returns whether this context contains any checkable assertions.
    #[must_use]
    pub fn has_assertions(&self) -> bool {
        use super::VerificationMode;
        use crate::vc::obligation::ObligationKind;

        self.obligations.iter().any(|o| match o.kind {
            ObligationKind::Assert
            | ObligationKind::Ensures
            | ObligationKind::MeasureDecreases
            | ObligationKind::MeasureNonNegative
            | ObligationKind::LoopInvariant
            | ObligationKind::InvariantExceptBreak
            | ObligationKind::LoopEnsures
            | ObligationKind::AssertBy => true,
            ObligationKind::Requires => self.verification_mode == VerificationMode::CallSite,
            // `Recommends` is advisory (soft-warning check), never a HARD assertion.
            ObligationKind::Recommends => false,
            ObligationKind::Assume
            | ObligationKind::PostLoopAssume
            | ObligationKind::BroadcastAssume
            | ObligationKind::LoopGuard => false,
            #[allow(unreachable_patterns)]
            _ => true,
        })
    }

    /// Returns whether this context contains any assumption obligations.
    #[must_use]
    pub fn has_assumptions(&self) -> bool {
        use super::VerificationMode;
        use crate::vc::obligation::ObligationKind;

        self.obligations.iter().any(|o| match o.kind {
            ObligationKind::Assume
            | ObligationKind::PostLoopAssume
            | ObligationKind::BroadcastAssume
            | ObligationKind::LoopGuard => true,
            ObligationKind::Requires => self.verification_mode == VerificationMode::BodyLevel,
            // `Recommends` is advisory (soft-warning check), never a HARD assumption.
            ObligationKind::Recommends => false,
            ObligationKind::Assert
            | ObligationKind::Ensures
            | ObligationKind::MeasureDecreases
            | ObligationKind::MeasureNonNegative
            | ObligationKind::LoopInvariant
            | ObligationKind::InvariantExceptBreak
            | ObligationKind::LoopEnsures
            | ObligationKind::AssertBy => false,
            #[allow(unreachable_patterns)]
            _ => false,
        })
    }

    /// Adds a non-negativity obligation for a termination measure.
    pub fn add_measure_nonneg(&mut self, measure_name: &str) {
        self.obligations.push(ProofObligation::measure_non_negative(
            format!("{}_nonneg", measure_name),
            format!("{} >= 0", measure_name),
        ));
    }

    /// Adds a lexicographic decrease obligation between old and new measure values.
    pub fn add_measure_decreases(&mut self, measure_name: &str, old_value: &str, new_value: &str) {
        let condition =
            crate::decreases_lex::lexicographic_decreases_condition(old_value, new_value);
        self.obligations.push(ProofObligation::measure_decreases(
            format!("{}_decreases", measure_name),
            condition,
        ));
    }

    fn sync_mode_behaviors(&mut self, mode: crate::mode::FunctionMode) {
        use super::{BitshiftBehavior, Div0Behavior, OverflowBehavior};

        if !self.overflow_behavior_explicit {
            self.overflow_behavior = OverflowBehavior::from_mode(mode);
        }
        if !self.div0_behavior_explicit {
            self.div0_behavior = Div0Behavior::from_mode(mode);
        }
        if !self.bitshift_behavior_explicit {
            self.bitshift_behavior = BitshiftBehavior::from_mode(mode);
        }
    }

    /// Sets the function context and syncs arithmetic behaviors from its mode.
    pub fn set_function_context(&mut self, context: FunctionContext) {
        self.sync_mode_behaviors(context.mode());
        self.function_context = Some(context);
    }
}
