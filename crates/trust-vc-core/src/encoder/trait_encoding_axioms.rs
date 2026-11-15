//! Trait method axiom emission and lowering helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use ay_dpll::api::{FuncDecl, Term};

use crate::encoder::ir_encoder::normalize;
use crate::encoder::types::sort_for_type;
use crate::encoder::{AYEncoder, AstExpressionParser};
use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::{LogicOp, TraitDecl, TraitImplDecl, TraitMethodDecl, TrustVcExpr, TrustVcType};
use crate::ir_lowering::{lower_syn_expr, MethodMeta, TypeEnv};

use super::super::trait_self_fields::PolySelfFieldProjection;

use super::{
    TraitEncoding, TRAIT_ENCODING_CONTEXT, TRAIT_RECEIVER_NAME, TRAIT_RECEIVER_TYPE_NAME,
    TRAIT_RESULT_NAME,
};

impl AYEncoder {
    /// Emits a per-impl body axiom for a default trait method that the impl
    /// does not override. The axiom shape is:
    /// ```text
    /// ∀(s:T, params). {Trait__method(Box_T(s), params...)}
    ///   Trait__method(Box_T(s), params...) == <default body with self=Box_T(s)>
    /// ```
    /// where `T` is this impl's own type. The default body is this impl's
    /// behaviour and no other receiver's: another impl may override the
    /// method, and a generic caller's receiver may be of any implementing type.
    pub(super) fn assert_default_body_axiom(
        &mut self,
        encoding: &TraitEncoding,
        impl_decl: &TraitImplDecl,
        method: &TraitMethodDecl,
        body_text: &str,
    ) -> TrustVcResult<()> {
        let projections = crate::encoder::trait_self_fields::poly_self_field_projections(
            &encoding.name,
            method,
            &[body_text],
        )?;
        self.declare_poly_self_field_ufs(&projections)?;

        let trait_method_fn = encoding.method_fns.get(&method.name).ok_or_else(|| {
            trait_encoding_error(format!(
                "Missing UF for default method '{}' in trait '{}'",
                method.name, encoding.name
            ))
        })?;

        // `self` ranges over this impl's type and reaches the trait UF as
        // `Box_T(self)`, so the axiom says nothing about the receiver of an
        // impl that overrides the method, or of a generic caller.
        let (box_fn, _unbox_fn) = self
            .registries
            .poly_context
            .ensure_box_unbox(&mut self.solver, &impl_decl.concrete_type)?;
        let self_var = self.solver.fresh_var(
            &format!(
                "__default_{}_{}_self_{}",
                sanitize_symbol(&encoding.name),
                sanitize_symbol(&method.name),
                sanitize_symbol(&impl_decl.concrete_type.to_type_string()),
            ),
            sort_for_type(&impl_decl.concrete_type),
        );
        let boxed_self = self.solver.try_apply(&box_fn, &[self_var]).map_err(|e| {
            trait_encoding_error(format!("Default body: box application failed: {e}"))
        })?;

        let mut bound_vars = vec![self_var];
        let mut trait_args = vec![boxed_self];

        // The body is encoded with `self` bound to the Poly term `Box_T(self)`.
        let mut local_bindings: Vec<(&str, Term)> = vec![(TRAIT_RECEIVER_NAME, boxed_self)];
        let mut local_types: Vec<(String, TrustVcType)> =
            vec![(TRAIT_RECEIVER_NAME.to_string(), TrustVcType::Poly)];

        for (param_name, param_ty) in &method.params {
            let param_var = self.solver.fresh_var(
                &format!(
                    "__default_{}_{}_{}_{}",
                    sanitize_symbol(&encoding.name),
                    sanitize_symbol(&method.name),
                    sanitize_symbol(param_name),
                    sanitize_symbol(&impl_decl.concrete_type.to_type_string()),
                ),
                sort_for_type(param_ty),
            );
            bound_vars.push(param_var);
            trait_args.push(param_var);
            local_bindings.push((param_name.as_str(), param_var));
            local_types.push((param_name.clone(), param_ty.clone()));
        }

        // LHS: Trait__method(Box_T(self), params...)
        let lhs = self
            .solver
            .try_apply(trait_method_fn, &trait_args)
            .map_err(|e| {
                trait_encoding_error(format!(
                    "Default body: trait method application failed: {e}"
                ))
            })?;

        // RHS: lower and encode the default body expression
        let trait_decl_for_env = TraitDecl {
            name: encoding.name.clone(),
            methods: encoding.methods.clone(),
            supertraits: Vec::new(),
            generics: encoding.generics.clone(),
        };
        let env = build_trait_contract_env(&trait_decl_for_env, method, &projections);
        let parsed: syn::Expr =
            syn::parse_str(body_text).map_err(|source| TrustVcError::Parse {
                context: "parse default body",
                source,
            })?;
        let body_expr = lower_syn_expr(&parsed, &env).map_err(|source| TrustVcError::Lowering {
            context: "lower default body",
            source: enrich_lowering_error(
                source,
                "default body",
                &encoding.name,
                &method.name,
                body_text,
            ),
        })?;

        // BINDER CAPTURE (CARDINAL), same encode-then-close shape as
        // `add_typed_broadcast`: the axiom body is encoded with every bound
        // variable resolved as an ordinary top-level term and only closed
        // afterwards. Announce the pending closure so the inlined helpers
        // decline their top-level hoist, and take an assertion watermark so the
        // general backstop can catch any helper that still hoists.
        // See `crate::encoder::binder_capture`.
        let capture_watermark = self.assertion_watermark();
        let rhs = crate::encoder::with_flag_unwind_safe!(
            self.state.pending_universal_closure,
            !bound_vars.is_empty(),
            { self.encode_trait_expr_with_bindings(&body_expr, &local_bindings, &local_types) }
        )?;

        // Assert: ∀(self:T, params). {Trait__method(Box_T(self), ...)} lhs == rhs
        let eq = self
            .solver
            .try_eq(lhs, rhs)
            .map_err(|e| trait_encoding_error(format!("Default body equality failed: {e}")))?;

        if let Some(capture) = self.binder_capture_since(capture_watermark, &bound_vars) {
            let site = format!("trait-default-body:{}::{}", encoding.name, method.name);
            self.record_binder_capture(&site, &capture);
            return Ok(());
        }

        let axiom = self
            .solver
            .try_forall_with_triggers(&bound_vars, eq, &[&[lhs]])
            .map_err(|e| {
                trait_encoding_error(format!(
                    "Default body axiom quantification failed for '{}::{}': {e}",
                    encoding.name, method.name
                ))
            })?;

        self.solver.try_assert_term(axiom).map_err(|e| {
            trait_encoding_error(format!(
                "Failed to assert default body axiom for '{}::{}': {e}",
                encoding.name, method.name
            ))
        })?;

        Ok(())
    }

    pub(super) fn declare_trait_method(
        &mut self,
        symbol: &str,
        method: &TraitMethodDecl,
    ) -> TrustVcResult<FuncDecl> {
        let mut domain_sorts = Vec::with_capacity(method.params.len() + 1);
        let mut param_types = Vec::with_capacity(method.params.len() + 1);
        domain_sorts.push(sort_for_type(&TrustVcType::Poly));
        param_types.push(TrustVcType::Poly);
        for (_, param_ty) in &method.params {
            domain_sorts.push(sort_for_type(param_ty));
            param_types.push(param_ty.clone());
        }

        let return_sort = sort_for_type(&method.return_type);
        let func_decl = self
            .solver
            .try_declare_fun(symbol, &domain_sorts, return_sort)
            .map_err(|err| trait_encoding_error(format!("Failed to declare '{symbol}': {err}")))?;

        self.fn_ctx
            .functions
            .insert(symbol.to_string(), func_decl.clone());
        self.fn_ctx
            .return_types
            .insert(symbol.to_string(), method.return_type.clone());
        self.fn_ctx
            .param_types
            .insert(symbol.to_string(), param_types.clone());

        // A parameterized trait method's bare-TypeParam slots are Poly-sorted in
        // the UF; registering the engaged type-param names here enables the
        // #2053 call-site bridging (concrete args boxed with a ground roundtrip
        // fact, Poly result unboxed) for concrete-receiver callers. Generic-
        // bound callers pass Poly-sorted args, which type-binding inference
        // deliberately skips — their behavior is unchanged.
        let mut engaged_type_params: Vec<String> = Vec::new();
        for ty in param_types
            .iter()
            .chain(std::iter::once(&method.return_type))
        {
            if let TrustVcType::TypeParam(name) = ty {
                if !engaged_type_params.contains(name) {
                    engaged_type_params.push(name.clone());
                }
            }
        }
        if !engaged_type_params.is_empty() {
            self.fn_ctx
                .type_params
                .insert(symbol.to_string(), engaged_type_params);
        }
        self.state
            .lowering_env
            .insert_fn(symbol.to_string(), method.return_type.clone());
        self.state
            .lowering_env
            .insert_fn_params(symbol.to_string(), param_types);

        Ok(func_decl)
    }

    pub(super) fn assert_trait_postconditions(
        &mut self,
        decl: &TraitDecl,
        method: &TraitMethodDecl,
        encoding: &TraitEncoding,
    ) -> TrustVcResult<()> {
        if method.ensures.is_empty() {
            return Ok(());
        }

        let projections = crate::encoder::trait_self_fields::poly_self_field_projections(
            &decl.name,
            method,
            &[],
        )?;
        self.declare_poly_self_field_ufs(&projections)?;

        let method_fn = encoding.method_fns.get(&method.name).ok_or_else(|| {
            trait_encoding_error(format!(
                "Trait '{}' missing method UF for '{}'",
                encoding.name, method.name
            ))
        })?;

        let mut bound_terms = Vec::with_capacity(method.params.len() + 1);
        let self_term = self.solver.fresh_var(
            &format!(
                "__trait_{}_{}_self",
                sanitize_symbol(&decl.name),
                sanitize_symbol(&method.name)
            ),
            sort_for_type(&TrustVcType::Poly),
        );
        bound_terms.push(self_term);

        let mut local_bindings: Vec<(&str, Term)> = Vec::with_capacity(method.params.len() + 2);
        local_bindings.push((TRAIT_RECEIVER_NAME, self_term));

        let mut local_types: Vec<(String, TrustVcType)> =
            Vec::with_capacity(method.params.len() + 2);
        local_types.push((TRAIT_RECEIVER_NAME.to_string(), TrustVcType::Poly));

        let mut app_args = Vec::with_capacity(method.params.len() + 1);
        app_args.push(self_term);
        for (param_name, param_ty) in &method.params {
            let param_term = self.solver.fresh_var(
                &format!(
                    "__trait_{}_{}_{}",
                    sanitize_symbol(&decl.name),
                    sanitize_symbol(&method.name),
                    sanitize_symbol(param_name)
                ),
                sort_for_type(param_ty),
            );
            bound_terms.push(param_term);
            app_args.push(param_term);
            local_bindings.push((param_name.as_str(), param_term));
            local_types.push((param_name.clone(), param_ty.clone()));
        }

        let result_term = self.solver.try_apply(method_fn, &app_args).map_err(|err| {
            trait_encoding_error(format!(
                "Failed to apply trait UF '{}': {}",
                method_fn.name(),
                err
            ))
        })?;
        local_bindings.push((TRAIT_RESULT_NAME, result_term));
        local_types.push((TRAIT_RESULT_NAME.to_string(), method.return_type.clone()));

        let env = build_trait_contract_env(decl, method, &projections);
        let requires =
            lower_contracts(&method.requires, &env, "requires", &decl.name, &method.name)?;
        let ensures = lower_contracts(&method.ensures, &env, "ensures", &decl.name, &method.name)?;

        let ensured = conjunction(ensures).ok_or_else(|| {
            trait_encoding_error(format!(
                "Trait method '{}::{}' has no postcondition to encode",
                decl.name, method.name
            ))
        })?;
        let axiom_expr = if let Some(required) = conjunction(requires) {
            TrustVcExpr::Implies {
                premise: Box::new(required),
                conclusion: Box::new(ensured),
            }
        } else {
            ensured
        };

        // BINDER CAPTURE (CARDINAL), same encode-then-close shape as
        // `add_typed_broadcast`: the axiom body is encoded with every bound
        // variable resolved as an ordinary top-level term and only closed
        // afterwards. Announce the pending closure so the inlined helpers
        // decline their top-level hoist, and take an assertion watermark so the
        // general backstop can catch any helper that still hoists.
        // See `crate::encoder::binder_capture`.
        let capture_watermark = self.assertion_watermark();
        let body = crate::encoder::with_flag_unwind_safe!(
            self.state.pending_universal_closure,
            !bound_terms.is_empty(),
            { self.encode_trait_expr_with_bindings(&axiom_expr, &local_bindings, &local_types) }
        )?;
        if let Some(capture) = self.binder_capture_since(capture_watermark, &bound_terms) {
            let site = format!("trait-postcondition:{}::{}", decl.name, method.name);
            self.record_binder_capture(&site, &capture);
            return Ok(());
        }
        let quantified = self
            .solver
            .try_forall_with_triggers(&bound_terms, body, &[&[result_term]])
            .map_err(|err| {
                trait_encoding_error(format!(
                    "Failed to quantify postcondition axiom for '{}::{}': {}",
                    decl.name, method.name, err
                ))
            })?;
        self.solver.try_assert_term(quantified).map_err(|err| {
            trait_encoding_error(format!(
                "Failed to assert postcondition axiom for '{}::{}': {}",
                decl.name, method.name, err
            ))
        })?;
        Ok(())
    }

    /// Declares a projection signature exactly once.  A same-name declaration
    /// with different metadata is a soundness error, not an idempotent hit.
    fn declare_poly_self_field_ufs(
        &mut self,
        projections: &[PolySelfFieldProjection],
    ) -> TrustVcResult<()> {
        for projection in projections {
            if self.fn_ctx.functions.contains_key(&projection.uf_name) {
                let return_matches = self.fn_ctx.return_types.get(&projection.uf_name)
                    == Some(&projection.field_type);
                let params_match = self
                    .fn_ctx
                    .param_types
                    .get(&projection.uf_name)
                    .is_some_and(|params| params == &[TrustVcType::Poly]);
                if return_matches && params_match {
                    continue;
                }
                return Err(trait_encoding_error(format!(
                    "conflicting declaration for self-field projection '{}'",
                    projection.uf_name
                )));
            }

            let domain = [sort_for_type(&TrustVcType::Poly)];
            let range = sort_for_type(&projection.field_type);
            let decl = self
                .solver
                .try_declare_fun(&projection.uf_name, &domain, range)
                .map_err(|err| {
                    trait_encoding_error(format!(
                        "Failed to declare self-field projection '{}': {err}",
                        projection.uf_name
                    ))
                })?;
            self.fn_ctx
                .functions
                .insert(projection.uf_name.clone(), decl);
            self.fn_ctx
                .return_types
                .insert(projection.uf_name.clone(), projection.field_type.clone());
            self.fn_ctx
                .param_types
                .insert(projection.uf_name.clone(), vec![TrustVcType::Poly]);
            self.state
                .lowering_env
                .insert_fn(projection.uf_name.clone(), projection.field_type.clone());
            self.state
                .lowering_env
                .insert_fn_params(projection.uf_name.clone(), vec![TrustVcType::Poly]);
        }
        Ok(())
    }

    /// Propagates each impl method's OWN declared `ensures` to concrete/UFCS
    /// callers as an additional postcondition axiom on the trait method UF,
    /// GUARDED to this impl:
    /// ```text
    ///   ∀ x:S, params. {T__f(Box_S(x), params)}  impl_ensures[result := T__f(Box_S(x), params)]
    /// ```
    /// The `Box_S(x)` guard makes the axiom impl-specific (a different impl's
    /// `Box_R(y)` term never matches the trigger), so distinct impls with
    /// contradictory `ensures` never collide. It reaches a concrete WITH-SELF
    /// receiver call `s.f(..)` (`s: S`), which lowers to `T__f(Box_S(s), ..)` via
    /// the impl's box bridge (`register_trait_impl_methods_for_concrete_types`).
    ///
    /// SOUNDNESS: this axiom is justified ENTIRELY by the conformance-extension
    /// (`build_impl_ensures_assert_obligations`) having verified `body ⊨
    /// impl_ensures` — exactly as the trait postcondition axiom is justified by
    /// the trait-`ensures` conformance check. It is emitted only for a
    /// NON-external impl (conformance skips an external one, so nothing would
    /// check the clause) and only for impl methods whose captured body the
    /// conformance pass checks; a body that violates its declared `ensures`
    /// Counterexamples in that pass (which runs after the main verification), so
    /// this axiom can never yield a lasting false `Verified`.
    ///
    /// PARAMETER SCOPE: the impl `ensures` is written in the IMPL's parameter
    /// names, which may rename or permute the trait's; it is registered only in
    /// its positional canonical form (`canonicalize_impl_method_ensures`), naming
    /// the i-th non-receiver parameter `__trust_vc_conf_arg_{i}` exactly as the
    /// captured body does. Here placeholder `i` binds UF argument `i`, and it is
    /// lowered and encoded in an env that holds ONLY `self`, `result` and the
    /// placeholders; the trait `requires` guard keeps the TRAIT's names in a
    /// separate env. The two scopes never meet, so no trait name can capture an
    /// identifier of the impl clause. An arity disagreement with the captured
    /// body skips the axiom. Reading the raw clause in the trait's names was a
    /// measured false verify (`impl_ensures_positional_binding_capability.rs`).
    ///
    /// A requires-bearing trait method is NOT skipped; it is GUARDED. The
    /// conformance pass assumes the trait `requires` (`build_contract_obligations`
    /// pushes each one as `ObligationKind::Assume`) before asserting the impl
    /// `ensures`, so the fact it discharges is exactly
    /// `requires ⟹ impl_ensures` — never the unconditional postcondition. The
    /// axiom therefore carries the same implication, mirroring
    /// `assert_trait_postconditions`. Emitting it unconditionally would claim the
    /// postcondition on inputs the impl was never checked against; dropping it
    /// (the previous behaviour) loses every ordinary "trait method with a
    /// precondition" call site. If ANY requires clause fails to lower against the
    /// minimal env, the whole axiom is skipped — an un-lowered premise must never
    /// weaken into an unconditional claim.
    ///
    /// An impl method with its OWN `requires` never reaches here at all:
    /// `capture_conformance_method_body` declines on it, so no body is captured
    /// and no `impl_ensures` is registered.
    ///
    /// Fail-closed skips (leave the caller without the strengthened
    /// postcondition; never emit an unjustified fact): a `Self`-returning
    /// (`Poly`) method, any clause — requires or ensures — that does not lower
    /// cleanly against a minimal (self/result/params) env, or any solver failure.
    pub(crate) fn assert_impl_postcondition_axioms(
        &mut self,
        impl_decl: &TraitImplDecl,
        impl_ensures_by_fn: &HashMap<crate::ir::ImplMethodKey, Vec<String>>,
        impl_bodies: &HashMap<crate::ir::ImplMethodKey, crate::ir::ConformanceMethodBody>,
    ) -> TrustVcResult<()> {
        // External impls are TRUSTED, not conformance-checked, so an impl
        // `ensures` published from one is an axiom nothing ever checks. Mirrors
        // `assert_impl_trait_ensures_concrete_axioms`.
        if impl_decl.is_external || impl_ensures_by_fn.is_empty() {
            return Ok(());
        }
        let Some(encoding) = self
            .registries
            .trait_encodings
            .get(&impl_decl.trait_name)
            .cloned()
        else {
            return Ok(());
        };
        let concrete_type = impl_decl.concrete_type.clone();

        // Declare the concrete self datatype's field SELECTORS in `fn_ctx.functions`
        // so a FIELD access in the impl ensures (`result == self.tag`, which lowers
        // to the FnCall `S_S_tag(self)`) resolves when `encode_trait_expr_with_bindings`
        // looks a call up by name. ay already registers these selectors from the
        // datatype declaration; the minimal trait-expr encoder resolves FnCalls
        // against `fn_ctx.functions` (which the datatype registration does NOT
        // populate — the main obligation path resolves selectors inline via
        // place_encoding). Without this the ensures fails to encode, the whole
        // impl-postcondition axiom is dropped, and the method UF is left
        // unconstrained → a spurious counterexample on the (true) impl ensures.
        if let TrustVcType::Datatype { name, variants } = &concrete_type {
            // Ensure the datatype is declared natively (idempotent under ay's
            // adopt-identical re-declaration) so its native selector exists to
            // link against below.
            let _ = self
                .solver
                .try_declare_datatype(&crate::encoder::datatype::datatype_sort_for(name, variants));
            let carrier = crate::encoder::datatype::datatype_carrier_sort(name);
            if let Some(variant) = variants.first() {
                for (idx, (field_name, field_ty)) in variant.fields.iter().enumerate() {
                    let selector_name = crate::encoder::datatype::selector_symbol_name(
                        name,
                        &variant.name,
                        field_name,
                        idx,
                    );
                    // Register a selector HANDLE whose signature MATCHES ay's
                    // native selector (carrier-sort domain, `field_sort_for`
                    // codomain), so the minimal trait-expr encoder resolves the
                    // FnCall `S_field(self)` the impl ensures lowers to.
                    let field_sort = crate::encoder::datatype::field_sort_for(name, field_ty);
                    let handle = self
                        .fn_ctx
                        .functions
                        .entry(selector_name.clone())
                        .or_insert_with(|| {
                            FuncDecl::new(
                                selector_name.clone(),
                                vec![carrier.clone()],
                                field_sort.clone(),
                            )
                        })
                        .clone();
                    // LINK the handle to ay's NATIVE datatype selector:
                    //   ∀self:S. {handle(self)} handle(self) == native_selector(self)
                    // Under AY 0.2 native datatypes a bare selector UF is
                    // unconstrained, so a FIELD-referencing impl ensures
                    // (`result == self.tag`) spuriously counterexampled. This
                    // definitional equality grounds `S_tag(self)` to the concrete
                    // field value. SOUND — it only defines the handle to BE the
                    // native selector; fail-open on any solver hiccup leaves the
                    // ensures fail-closed (never a false verify).
                    let self_var = self.solver.fresh_var(
                        &format!(
                            "__sellink_{}_{}_self",
                            sanitize_symbol(name),
                            sanitize_symbol(field_name)
                        ),
                        carrier.clone(),
                    );
                    //
                    // ONLY when the handle is a DISTINCT symbol. `selector_symbol_name`
                    // is the native selector's own name (`datatype.rs` reuses the exact
                    // native symbols), so `try_apply(handle)` and
                    // `try_datatype_selector` normally yield the SAME term and the
                    // equality folds to `true`. Asserting `∀self:S. true` is not a
                    // harmless no-op: ay (0787f78bd) reports the whole query
                    // `Unknown(QuantifierUnhandled)` when that vacuous
                    // datatype-sorted binder is present — measured on the
                    // concrete_trait_method_call_site `field_pos` query (faithful
                    // SMT2 repro: with the `(forall ((s S)) true)` line Unknown/
                    // QuantifierUnhandled, without it unsat in 4ms), which is why
                    // every impl-ensures-over-a-field call site and
                    // concrete_trait_method_resolution::impl_ensures_reaches_concrete_caller
                    // came back NotProved. A definitional link between one term and
                    // itself carries no information, so it is skipped outright.
                    if let (Ok(handle_app), Ok(native)) = (
                        self.solver.try_apply(&handle, &[self_var]),
                        self.solver
                            .try_datatype_selector(&selector_name, self_var, field_sort),
                    ) {
                        if handle_app == native {
                            continue;
                        }
                        if let Ok(eq) = self.solver.try_eq(handle_app, native) {
                            if let Ok(axiom) = self.solver.try_forall_with_triggers(
                                &[self_var],
                                eq,
                                &[&[handle_app]],
                            ) {
                                let _ = self.solver.try_assert_term(axiom);
                            }
                        }
                    }
                }
            }
        }

        for (trait_method_name, concrete_fn_name) in &impl_decl.method_bindings {
            // The shared concrete symbol is not an identity — see
            // `TraitImplDecl::inherent_shadowed_methods`. `impl_ensures_by_fn` is
            // keyed by the trait-erased `Type__method` string, so when another
            // declaration owns that symbol this lookup can return a DIFFERENT
            // impl's `ensures`; publish nothing rather than the wrong contract.
            if !impl_decl.may_claim_concrete_symbol(trait_method_name) {
                continue;
            }
            let impl_method_key =
                crate::ir::ImplMethodKey::new(&impl_decl.trait_name, concrete_fn_name);
            let Some(impl_ensures) = impl_ensures_by_fn.get(&impl_method_key) else {
                continue;
            };
            if impl_ensures.is_empty() {
                continue;
            }
            let Some(method) = encoding
                .methods
                .iter()
                .find(|method| method.name == *trait_method_name)
            else {
                continue;
            };
            // Fail-closed skips (see doc comment). TypeParam-bearing signatures
            // are gated OFF deterministically: instantiated impl-ensures
            // propagation is A2-conformance work, and publishing a strengthened
            // ensures over Poly-erased slots without an instantiation-aware
            // conformance check would be the cardinal unchecked-axiom leak.
            if method.return_type == TrustVcType::Poly
                || method.return_type.contains_type_param()
                || method
                    .params
                    .iter()
                    .any(|(_, param_ty)| param_ty.contains_type_param())
            {
                continue;
            }
            // POSITIONAL SCOPE (see doc comment): the registered clauses name the
            // impl's parameters only as `__trust_vc_conf_arg_{i}`. Publish only
            // when the captured body — the conformance pass's positional anchor —
            // agrees on the arity, and only when no trait name can collide with
            // the receiver/result/placeholder names.
            if impl_bodies
                .get(&impl_method_key)
                .is_none_or(|body| body.param_count != method.params.len())
            {
                continue;
            }
            if method.params.iter().any(|(param_name, _)| {
                param_name == TRAIT_RECEIVER_NAME
                    || param_name == TRAIT_RESULT_NAME
                    || param_name.starts_with("__trust_vc_")
            }) {
                continue;
            }
            let Some(method_fn) = encoding.method_fns.get(trait_method_name).cloned() else {
                continue;
            };
            let placeholder_names: Vec<String> = (0..method.params.len())
                .map(|index| format!("__trust_vc_conf_arg_{index}"))
                .collect();

            let mut bound_terms: Vec<Term> = Vec::new();
            let mut app_args: Vec<Term> = Vec::new();
            // `self`/`result` go into BOTH binding lists; the impl `ensures` sees
            // the positional placeholders, the trait `requires` the trait names.
            let mut ensures_bindings: Vec<(&str, Term)> = Vec::new();
            let mut requires_bindings: Vec<(&str, Term)> = Vec::new();
            let mut local_types: Vec<(String, TrustVcType)> = Vec::new();

            // Box the concrete self so the axiom is guarded to THIS impl. Every
            // trait method UF (incl. a no-self associated function, via its
            // phantom boxed self) carries a `Poly` self.
            {
                let box_fn = match self
                    .registries
                    .poly_context
                    .ensure_box_unbox(&mut self.solver, &concrete_type)
                {
                    Ok((box_fn, _unbox)) => box_fn,
                    Err(_) => continue,
                };
                let self_var = self.solver.fresh_var(
                    &format!(
                        "__implpost_{}_{}_self",
                        sanitize_symbol(&impl_decl.trait_name),
                        sanitize_symbol(trait_method_name),
                    ),
                    sort_for_type(&concrete_type),
                );
                let boxed = match self.solver.try_apply(&box_fn, &[self_var]) {
                    Ok(term) => term,
                    Err(_) => continue,
                };
                bound_terms.push(self_var);
                app_args.push(boxed);
                ensures_bindings.push((TRAIT_RECEIVER_NAME, self_var));
                requires_bindings.push((TRAIT_RECEIVER_NAME, self_var));
                local_types.push((TRAIT_RECEIVER_NAME.to_string(), concrete_type.clone()));
            }

            for ((param_name, param_ty), placeholder) in
                method.params.iter().zip(placeholder_names.iter())
            {
                let param_var = self.solver.fresh_var(
                    &format!(
                        "__implpost_{}_{}_{}",
                        sanitize_symbol(&impl_decl.trait_name),
                        sanitize_symbol(trait_method_name),
                        sanitize_symbol(param_name),
                    ),
                    sort_for_type(param_ty),
                );
                bound_terms.push(param_var);
                app_args.push(param_var);
                ensures_bindings.push((placeholder.as_str(), param_var));
                requires_bindings.push((param_name.as_str(), param_var));
                local_types.push((placeholder.clone(), param_ty.clone()));
                local_types.push((param_name.clone(), param_ty.clone()));
            }

            let app = match self.solver.try_apply(&method_fn, &app_args) {
                Ok(term) => term,
                Err(_) => continue,
            };
            ensures_bindings.push((TRAIT_RESULT_NAME, app));
            requires_bindings.push((TRAIT_RESULT_NAME, app));
            local_types.push((TRAIT_RESULT_NAME.to_string(), method.return_type.clone()));

            // Minimal envs: self (concrete), result, and the parameters under the
            // naming of the scope that WROTE the clause. Intentionally carry NO
            // trait-method metadata, so a clause invoking `self.m()` fails to
            // lower and is skipped — conservative, since conformance still checks
            // it and the caller simply doesn't gain that (harder) clause.
            let mut ensures_env = TypeEnv::new();
            ensures_env.insert(TRAIT_RECEIVER_NAME.to_string(), concrete_type.clone());
            ensures_env.insert(TRAIT_RESULT_NAME.to_string(), method.return_type.clone());
            for ((_, param_ty), placeholder) in method.params.iter().zip(placeholder_names.iter()) {
                ensures_env.insert(placeholder.clone(), param_ty.clone());
            }
            let mut requires_env = TypeEnv::new();
            requires_env.insert(TRAIT_RECEIVER_NAME.to_string(), concrete_type.clone());
            requires_env.insert(TRAIT_RESULT_NAME.to_string(), method.return_type.clone());
            for (param_name, param_ty) in &method.params {
                requires_env.insert(param_name.clone(), param_ty.clone());
            }

            let mut lowered_clauses = Vec::with_capacity(impl_ensures.len());
            let mut lowering_ok = true;
            for clause in impl_ensures {
                let parsed: syn::Expr = match syn::parse_str(clause) {
                    Ok(expr) => expr,
                    Err(_) => {
                        lowering_ok = false;
                        break;
                    }
                };
                match lower_syn_expr(&parsed, &ensures_env) {
                    Ok(expr) => lowered_clauses.push(expr),
                    Err(_) => {
                        lowering_ok = false;
                        break;
                    }
                }
            }
            if !lowering_ok {
                continue;
            }
            let Some(ensured) = conjunction(lowered_clauses) else {
                continue;
            };

            // GUARD by the trait method's `requires`. The conformance pass
            // assumes each one (`build_contract_obligations`, ObligationKind::
            // Assume) before asserting `body ⊨ impl_ensures`, so the implication
            // — and ONLY the implication — is the fact it discharges. A requires
            // clause that does not lower cleanly drops the ENTIRE axiom:
            // proceeding without the premise would publish the conclusion
            // unconditionally, which is the unsound direction.
            let mut lowered_requires = Vec::with_capacity(method.requires.len());
            let mut requires_lowering_ok = true;
            for clause in &method.requires {
                let parsed: syn::Expr = match syn::parse_str(clause) {
                    Ok(expr) => expr,
                    Err(_) => {
                        requires_lowering_ok = false;
                        break;
                    }
                };
                match lower_syn_expr(&parsed, &requires_env) {
                    Ok(expr) => lowered_requires.push(expr),
                    Err(_) => {
                        requires_lowering_ok = false;
                        break;
                    }
                }
            }
            if !requires_lowering_ok {
                continue;
            }
            let required = conjunction(lowered_requires);

            // See `crate::encoder::binder_capture` — encode-then-close, so the
            // pending closure must be announced and the hoist watermark taken.
            // The conclusion and the premise are ENCODED in their own scopes and
            // joined as terms, so neither binding list can reach the other's
            // clause.
            let capture_watermark = self.assertion_watermark();
            let body = match crate::encoder::with_flag_unwind_safe!(
                self.state.pending_universal_closure,
                !bound_terms.is_empty(),
                {
                    self.encode_trait_expr_with_bindings(&ensured, &ensures_bindings, &local_types)
                        .and_then(|ensured_term| match &required {
                            None => Ok(ensured_term),
                            Some(required) => {
                                let required_term = self.encode_trait_expr_with_bindings(
                                    required,
                                    &requires_bindings,
                                    &local_types,
                                )?;
                                self.solver
                                    .try_implies(required_term, ensured_term)
                                    .map_err(|err| {
                                        trait_encoding_error(format!(
                                            "Failed to guard impl ensures for '{}': {err}",
                                            method.name
                                        ))
                                    })
                            }
                        })
                }
            ) {
                Ok(term) => term,
                Err(_) => continue,
            };
            if let Some(capture) = self.binder_capture_since(capture_watermark, &bound_terms) {
                let site = format!("trait-impl-ensures:{}", method.name);
                self.record_binder_capture(&site, &capture);
                continue;
            }
            // `bound_terms` always carries at least the boxed self, so the axiom
            // is always quantified (triggered on the boxed application).
            let axiom = match self
                .solver
                .try_forall_with_triggers(&bound_terms, body, &[&[app]])
            {
                Ok(term) => term,
                Err(_) => continue,
            };
            let _ = self.solver.try_assert_term(axiom);
        }
        Ok(())
    }

    /// Propagates a trait method's `ensures` to concrete-receiver callers as a
    /// postcondition axiom about the PER-IMPL CONCRETE function, with the
    /// method's associated-type projections resolved to this impl's bindings so
    /// the axiom is CONCRETELY SORTED:
    /// ```text
    ///   ∀ self:S, params. {impl_fn(self, params)}
    ///     trait_ensures[result := impl_fn(self, params)]
    /// ```
    /// This is the associated-spec-fn (Phase A3) client seam. The shared per-trait
    /// method UF (`Trait__m`) is declared ONCE from the DECLARED signature, so its
    /// return slot for an `Self::Assoc`-typed method is the erased `Poly`/`Int`
    /// sort; a clause like `result == 7` over that slot fails to encode (sort
    /// mismatch), which is exactly why the shared-UF postcondition axiom
    /// (`assert_trait_postconditions`) and the impl-ensures axiom
    /// (`assert_impl_postcondition_axioms`) both silently drop associated-type
    /// methods. Binding `result` to the impl's OWN concrete function
    /// (`impl_fn : S -> ConcreteAssoc`) instead lets the projected type land in
    /// its concrete sort, so a caller of `s.produce()` can consume the trait
    /// contract.
    ///
    /// SOUNDNESS — the cardinal trait invariant: this axiom is a FORGED FACT
    /// unless the impl body actually discharges the trait `ensures`. It is
    /// justified ENTIRELY by the per-impl conformance pass
    /// (`verify_trait_conformance_obligation`), which checks `body ⊨ trait_ensures`
    /// with EXACTLY these resolved-concrete sorts (the baseline probe shows a
    /// `3u64` body against `result == 7` Counterexampling on
    /// `__trust_vc_impl_result`). A non-conforming impl is refuted on its own
    /// first-class conformance obligation, so the file cannot verify — precisely
    /// as the trait postcondition axiom is justified by the same pass. Emitted
    /// only for a NON-external impl method whose signature this impl resolves
    /// FULLY CONCRETE and whose `ensures` lowers cleanly; every other shape leaves
    /// the caller WITHOUT the strengthened postcondition (fail-closed — never an
    /// unjustified fact). Restricted to associated-type-bearing signatures so the
    /// working shared-UF path for ordinary methods is untouched.
    pub(crate) fn assert_impl_trait_ensures_concrete_axioms(
        &mut self,
        trait_decl: &TraitDecl,
        impl_decl: &TraitImplDecl,
    ) -> TrustVcResult<()> {
        // External impls are TRUSTED, not conformance-checked (their bodies may
        // deliberately diverge). Emitting this axiom would be an unjustified fact.
        if impl_decl.is_external {
            return Ok(());
        }

        // Instantiate a parameterized trait's type params at the impl's trait
        // type args, mirroring `synthesize_impl_method_contexts` so the concrete
        // fn's DECLARED sorts and this axiom's argument sorts agree.
        let generic_bindings: Vec<(String, TrustVcType)> = if !trait_decl.generics.is_empty()
            && trait_decl.generics.len() == impl_decl.trait_type_args.len()
            && impl_decl
                .trait_type_args
                .iter()
                .all(crate::trait_instantiation::is_fully_concrete)
        {
            trait_decl
                .generics
                .iter()
                .cloned()
                .zip(impl_decl.trait_type_args.iter().cloned())
                .collect()
        } else {
            Vec::new()
        };
        let bind_ty = |ty: &TrustVcType| {
            crate::ir_lowering::substitute_type_params(
                &impl_decl.resolve_assoc_projections(ty),
                &generic_bindings,
            )
        };

        for (trait_method_name, concrete_fn_name) in &impl_decl.method_bindings {
            // This axiom asserts the TRAIT's `ensures` directly about the bare
            // concrete symbol `Type__method`, with NO box guard — so it is the
            // most direct route by which a trait contract reaches a call site
            // that resolved to some other declaration of that name. Gate it on
            // the same resolution the linking axiom uses.
            if !impl_decl.may_claim_concrete_symbol(trait_method_name) {
                continue;
            }
            let Some(method) = trait_decl
                .methods
                .iter()
                .find(|method| method.name == *trait_method_name)
            else {
                continue;
            };
            // Nothing to propagate, or a requires-bearing method (the caller-side
            // requires-discharge map skips these — never publish a contract whose
            // precondition nothing establishes).
            if method.ensures.is_empty() || !method.requires.is_empty() {
                continue;
            }

            // SCOPE GATE: only signatures whose associated-type projections THIS
            // impl actually resolves. An ordinary method keeps the existing
            // shared-UF postcondition path untouched (this axiom would be
            // redundant there, and narrowing keeps the blast radius minimal).
            let signature_has_resolved_projection = method
                .params
                .iter()
                .map(|(_, ty)| ty)
                .chain(std::iter::once(&method.return_type))
                .any(|ty| impl_decl.resolve_assoc_projections(ty) != *ty);
            if !signature_has_resolved_projection {
                continue;
            }

            let return_ty = bind_ty(&method.return_type);
            let param_tys: Vec<(String, TrustVcType)> = method
                .params
                .iter()
                .map(|(name, ty)| (name.clone(), bind_ty(ty)))
                .collect();
            // Fail closed unless every position resolved to a concrete, boxable
            // sort — an unresolved projection stays Opaque, a bare param stays
            // TypeParam; either would sort-diverge from the concrete fn.
            if !crate::trait_instantiation::is_fully_concrete(&return_ty)
                || param_tys
                    .iter()
                    .any(|(_, ty)| !crate::trait_instantiation::is_fully_concrete(ty))
            {
                continue;
            }

            // The per-impl concrete function, declared by
            // `synthesize_impl_method_contexts` with exactly these resolved sorts.
            let Some(impl_fn) = self.fn_ctx.functions.get(concrete_fn_name).cloned() else {
                continue;
            };

            let mut bound_terms: Vec<Term> = Vec::with_capacity(param_tys.len() + 1);
            let mut app_args: Vec<Term> = Vec::with_capacity(param_tys.len() + 1);
            let mut local_bindings: Vec<(&str, Term)> = Vec::with_capacity(param_tys.len() + 2);
            let mut local_types: Vec<(String, TrustVcType)> =
                Vec::with_capacity(param_tys.len() + 2);

            let self_var = self.solver.fresh_var(
                &format!(
                    "__assocpost_{}_{}_self",
                    sanitize_symbol(&impl_decl.trait_name),
                    sanitize_symbol(trait_method_name),
                ),
                sort_for_type(&impl_decl.concrete_type),
            );
            bound_terms.push(self_var);
            app_args.push(self_var);
            local_bindings.push((TRAIT_RECEIVER_NAME, self_var));
            local_types.push((
                TRAIT_RECEIVER_NAME.to_string(),
                impl_decl.concrete_type.clone(),
            ));

            for (param_name, param_ty) in &param_tys {
                let param_var = self.solver.fresh_var(
                    &format!(
                        "__assocpost_{}_{}_{}",
                        sanitize_symbol(&impl_decl.trait_name),
                        sanitize_symbol(trait_method_name),
                        sanitize_symbol(param_name),
                    ),
                    sort_for_type(param_ty),
                );
                bound_terms.push(param_var);
                app_args.push(param_var);
                local_bindings.push((param_name.as_str(), param_var));
                local_types.push((param_name.clone(), param_ty.clone()));
            }

            // Apply the CONCRETE fn. `try_apply` sort-checks against its declared
            // domain, so any residual sort divergence fails closed here.
            let app = match self.solver.try_apply(&impl_fn, &app_args) {
                Ok(term) => term,
                Err(_) => continue,
            };
            local_bindings.push((TRAIT_RESULT_NAME, app));
            local_types.push((TRAIT_RESULT_NAME.to_string(), return_ty.clone()));

            // Minimal env: self/result/params at their CONCRETE types. No trait
            // metadata, so an `ensures` clause invoking `self.m()` fails to lower
            // and is skipped fail-closed (conformance still checks it).
            let mut env = TypeEnv::new();
            env.insert(
                TRAIT_RECEIVER_NAME.to_string(),
                impl_decl.concrete_type.clone(),
            );
            env.insert(TRAIT_RESULT_NAME.to_string(), return_ty.clone());
            for (param_name, param_ty) in &param_tys {
                env.insert(param_name.clone(), param_ty.clone());
            }

            let mut lowered_clauses = Vec::with_capacity(method.ensures.len());
            let mut lowering_ok = true;
            for clause in &method.ensures {
                let Ok(parsed) = syn::parse_str::<syn::Expr>(clause) else {
                    lowering_ok = false;
                    break;
                };
                match lower_syn_expr(&parsed, &env) {
                    Ok(expr) => lowered_clauses.push(expr),
                    Err(_) => {
                        lowering_ok = false;
                        break;
                    }
                }
            }
            if !lowering_ok {
                continue;
            }
            let Some(ensured) = conjunction(lowered_clauses) else {
                continue;
            };

            // See `crate::encoder::binder_capture` — encode-then-close, so the
            // pending closure must be announced and the hoist watermark taken.
            let capture_watermark = self.assertion_watermark();
            let body = match crate::encoder::with_flag_unwind_safe!(
                self.state.pending_universal_closure,
                !bound_terms.is_empty(),
                { self.encode_trait_expr_with_bindings(&ensured, &local_bindings, &local_types) }
            ) {
                Ok(term) => term,
                Err(_) => continue,
            };
            if let Some(capture) = self.binder_capture_since(capture_watermark, &bound_terms) {
                let site = format!("trait-impl-ensures-concrete:{}", method.name);
                self.record_binder_capture(&site, &capture);
                continue;
            }
            let axiom = match self
                .solver
                .try_forall_with_triggers(&bound_terms, body, &[&[app]])
            {
                Ok(term) => term,
                Err(_) => continue,
            };
            let _ = self.solver.try_assert_term(axiom);
        }
        Ok(())
    }

    fn encode_trait_expr_with_bindings(
        &mut self,
        expr: &TrustVcExpr,
        bindings: &[(&str, Term)],
        local_types: &[(String, TrustVcType)],
    ) -> TrustVcResult<Term> {
        let locals: HashMap<String, TrustVcType> = local_types.iter().cloned().collect();
        self.validate_ir_typing(expr, Some(&locals))?;
        let normalized = if !self.state.equality_assumptions.is_empty() {
            normalize::substitute_and_normalize(expr, &self.state.equality_assumptions)
        } else {
            normalize::normalize_int_expr(expr)
        };

        let mut ast_parser = AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.fn_ctx.functions,
        );
        ast_parser.function_return_types = Some(&self.fn_ctx.return_types);
        ast_parser.function_param_types = Some(&self.fn_ctx.param_types);
        ast_parser.function_type_params = Some(&self.fn_ctx.type_params);
        ast_parser.poly_context = Some(&mut self.registries.poly_context);
        ast_parser.ground_pool = Some(&mut self.state.ground_pool);
        ast_parser.choose_registry = Some(&mut self.registries.choose_registry);
        ast_parser.prophecy_registry = Some(&mut self.registries.prophecy_registry);
        ast_parser.in_assumption_context = true;
        // A trait axiom is asserted without its side conditions.
        ast_parser.obligations_unchecked = true;
        ast_parser.pending_universal_closure = self.state.pending_universal_closure;
        // See `eval::condition` — every parser that can encode a collection
        // length must agree about which lengths are `usize`-bounded, or two
        // encodings of the same proposition mint unrelated length companions.
        ast_parser
            .usize_bounded_lens
            .clone_from(&self.state.usize_bounded_lens);

        let local_type_map: HashMap<&str, &TrustVcType> = local_types
            .iter()
            .map(|(name, ty)| (name.as_str(), ty))
            .collect();
        for (name, term) in bindings {
            let ty = local_type_map
                .get(name)
                .ok_or_else(|| TrustVcError::Internal {
                    context: "encode trait expr",
                    detail: format!("Missing local type for trait binding '{name}'"),
                })?;
            ast_parser.local_vars.insert((*name).to_string(), *term);
            ast_parser
                .local_var_types
                .insert((*name).to_string(), (*ty).clone());
        }

        let result = ast_parser.encode_trust_vc_expr(&normalized);
        self.state.diagnostics.merge(&ast_parser.diagnostics);
        result
    }
}

fn build_trait_contract_env(
    decl: &TraitDecl,
    method: &TraitMethodDecl,
    projections: &[PolySelfFieldProjection],
) -> TypeEnv {
    let mut env = TypeEnv::new();
    env.insert(TRAIT_RECEIVER_NAME.to_string(), TrustVcType::Poly);
    env.insert(TRAIT_RESULT_NAME.to_string(), method.return_type.clone());
    for (param_name, param_ty) in &method.params {
        env.insert(param_name.clone(), param_ty.clone());
    }
    for projection in projections {
        env.insert_field_metadata(
            TRAIT_RECEIVER_TYPE_NAME.to_string(),
            projection.field_name.clone(),
            projection.uf_name.clone(),
            projection.field_type.clone(),
        );
    }
    for trait_method in &decl.methods {
        env.insert_method_metadata(
            TRAIT_RECEIVER_TYPE_NAME.to_string(),
            trait_method.name.clone(),
            MethodMeta {
                uf_name: trait_method_symbol(&decl.name, &trait_method.name),
                return_type: trait_method.return_type.clone(),
                param_types: trait_method
                    .params
                    .iter()
                    .map(|(_, ty)| ty.clone())
                    .collect(),
                box_receiver: None,
            },
        );
        // H10 (method half): the call site refuses a method whose own generic
        // parameters no argument carries, and needs the declaration order to
        // map a turbofish onto the carrying positions.
        env.insert_method_generic_params(
            TRAIT_RECEIVER_TYPE_NAME.to_string(),
            trait_method.name.clone(),
            trait_method.generic_params.clone(),
        );
    }
    env
}

fn lower_contracts(
    contracts: &[String],
    env: &TypeEnv,
    kind: &'static str,
    trait_name: &str,
    method_name: &str,
) -> TrustVcResult<Vec<TrustVcExpr>> {
    contracts
        .iter()
        .map(|contract| {
            let parsed: syn::Expr =
                syn::parse_str(contract).map_err(|source| TrustVcError::Parse {
                    context: "parse trait contract",
                    source,
                })?;
            lower_syn_expr(&parsed, env).map_err(|source| TrustVcError::Lowering {
                context: "lower trait contract",
                source: enrich_lowering_error(source, kind, trait_name, method_name, contract),
            })
        })
        .collect()
}

fn conjunction(exprs: Vec<TrustVcExpr>) -> Option<TrustVcExpr> {
    let mut exprs = exprs.into_iter();
    let first = exprs.next()?;
    Some(exprs.fold(first, |left, right| TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(left),
        right: Box::new(right),
    }))
}

pub(super) fn trait_method_symbol(trait_name: &str, method_name: &str) -> String {
    format!("{trait_name}__{method_name}")
}

pub(super) use crate::encoder::sanitize_symbol;

pub(super) fn trait_encoding_error(detail: impl Into<String>) -> TrustVcError {
    TrustVcError::Encoding {
        context: TRAIT_ENCODING_CONTEXT,
        detail: detail.into(),
    }
}

fn enrich_lowering_error(
    source: crate::ir_lowering::LoweringError,
    kind: &str,
    trait_name: &str,
    method_name: &str,
    contract: &str,
) -> crate::ir_lowering::LoweringError {
    use crate::ir_lowering::LoweringError;

    let detail = format!(
        "trait {kind} for '{trait_name}::{method_name}' failed to lower: {contract} ({source})"
    );
    match source {
        LoweringError::UnsupportedExpr(_) => LoweringError::UnsupportedExpr(detail),
        LoweringError::UnsupportedBinOp(_) => LoweringError::UnsupportedBinOp(detail),
        LoweringError::UnsupportedUnOp(_) => LoweringError::UnsupportedUnOp(detail),
        LoweringError::UnresolvedVar(_) => LoweringError::UnresolvedVar(detail),
        LoweringError::TypeInference(_) => LoweringError::TypeInference(detail),
        LoweringError::InvalidType(_) => LoweringError::InvalidType(detail),
        LoweringError::InvalidLiteral(_) => LoweringError::InvalidLiteral(detail),
        LoweringError::UnsupportedMethod(_) => LoweringError::UnsupportedMethod(detail),
        LoweringError::UnsupportedPattern(_) => LoweringError::UnsupportedPattern(detail),
        LoweringError::MissingElseBranch => LoweringError::UnsupportedExpr(detail),
        LoweringError::EmptyBlock => LoweringError::UnsupportedExpr(detail),
        LoweringError::InvalidCast(_) => LoweringError::InvalidCast(detail),
        // Diagnostic-parity variants carry byte-exact upstream Verus messages
        // (#2778); their text is load-bearing for `assert_vir_error_msg`
        // substring matching, so pass them through unchanged rather than
        // wrapping them in the enriched `detail` string.
        diagnostic_parity @ (LoweringError::IntegerLiteralOutOfRange(_)
        | LoweringError::BitVectorUnsupportedType(_)
        | LoweringError::BitShiftPossiblyNegativeShift(_)) => diagnostic_parity,
        LoweringError::ExpressionTooDeep { .. } => LoweringError::ExpressionTooDeep {
            limit: crate::expr_depth::MAX_EXPR_DEPTH,
            stage: "trait contract lowering",
        },
    }
}
