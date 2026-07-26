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

use super::{
    TraitEncoding, TRAIT_ENCODING_CONTEXT, TRAIT_RECEIVER_NAME, TRAIT_RECEIVER_TYPE_NAME,
    TRAIT_RESULT_NAME,
};

impl AYEncoder {
    /// Emits a per-impl body axiom for a default trait method that the impl
    /// does not override. The axiom shape is:
    /// ```text
    /// ∀(p:Poly, params). {Trait__method(p, params...)}
    ///   Trait__method(p, params...) == <default body with self=p>
    /// ```
    /// Uses Poly-sorted bound variable for ay-dpll E-matching compatibility.
    /// Part of #2442.
    pub(super) fn assert_default_body_axiom(
        &mut self,
        encoding: &TraitEncoding,
        impl_decl: &TraitImplDecl,
        method: &TraitMethodDecl,
        body_text: &str,
    ) -> TrustVcResult<()> {
        let trait_method_fn = encoding.method_fns.get(&method.name).ok_or_else(|| {
            trait_encoding_error(format!(
                "Missing UF for default method '{}' in trait '{}'",
                method.name, encoding.name
            ))
        })?;

        // Use Poly-sorted bound variable — ay-dpll E-matching only fires
        // for uninterpreted-sort variables (Poly), not Bool-sorted ones.
        let poly_sort = sort_for_type(&TrustVcType::Poly);
        let self_poly = self.solver.fresh_var(
            &format!(
                "__default_{}_{}_self",
                sanitize_symbol(&encoding.name),
                sanitize_symbol(&method.name),
            ),
            poly_sort,
        );

        let mut bound_vars = vec![self_poly];
        let mut trait_args = vec![self_poly];

        // Build local bindings for encoding the body: self -> self_poly (Poly-typed)
        let mut local_bindings: Vec<(&str, Term)> = vec![(TRAIT_RECEIVER_NAME, self_poly)];
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

        // LHS: Trait__method(self_poly, params...)
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
        let env = build_trait_contract_env(&trait_decl_for_env, method);
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

        let rhs =
            self.encode_trait_expr_with_bindings(&body_expr, &local_bindings, &local_types)?;

        // Assert: ∀(p:Poly, params). {Trait__method(p, ...)} lhs == rhs
        let eq = self
            .solver
            .try_eq(lhs, rhs)
            .map_err(|e| trait_encoding_error(format!("Default body equality failed: {e}")))?;

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

        let env = build_trait_contract_env(decl, method);
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

        let body =
            self.encode_trait_expr_with_bindings(&axiom_expr, &local_bindings, &local_types)?;
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
    /// the trait-`ensures` conformance check. It is emitted only for impl methods
    /// whose captured body the conformance pass checks; a body that violates its
    /// declared `ensures` Counterexamples in that pass (which runs after the main
    /// verification), so this axiom can never yield a lasting false `Verified`.
    ///
    /// Fail-closed skips (leave the caller without the strengthened
    /// postcondition; never emit an unjustified fact): a requires-bearing trait
    /// method, a `Self`-returning (`Poly`) method, any clause that does not lower
    /// cleanly against a minimal (self/result/params) env, or any solver failure.
    pub(crate) fn assert_impl_postcondition_axioms(
        &mut self,
        impl_decl: &TraitImplDecl,
        impl_ensures_by_fn: &HashMap<String, Vec<String>>,
    ) -> TrustVcResult<()> {
        if impl_ensures_by_fn.is_empty() {
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
                    if let (Ok(handle_app), Ok(native)) = (
                        self.solver.try_apply(&handle, &[self_var]),
                        self.solver
                            .try_datatype_selector(&selector_name, self_var, field_sort),
                    ) {
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
            let Some(impl_ensures) = impl_ensures_by_fn.get(concrete_fn_name) else {
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
            if !method.requires.is_empty()
                || method.return_type == TrustVcType::Poly
                || method.return_type.contains_type_param()
                || method
                    .params
                    .iter()
                    .any(|(_, param_ty)| param_ty.contains_type_param())
            {
                continue;
            }
            let Some(method_fn) = encoding.method_fns.get(trait_method_name).cloned() else {
                continue;
            };

            let mut bound_terms: Vec<Term> = Vec::new();
            let mut app_args: Vec<Term> = Vec::new();
            let mut local_bindings: Vec<(&str, Term)> = Vec::new();
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
                local_bindings.push((TRAIT_RECEIVER_NAME, self_var));
                local_types.push((TRAIT_RECEIVER_NAME.to_string(), concrete_type.clone()));
            }

            for (param_name, param_ty) in &method.params {
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
                local_bindings.push((param_name.as_str(), param_var));
                local_types.push((param_name.clone(), param_ty.clone()));
            }

            let app = match self.solver.try_apply(&method_fn, &app_args) {
                Ok(term) => term,
                Err(_) => continue,
            };
            local_bindings.push((TRAIT_RESULT_NAME, app));
            local_types.push((TRAIT_RESULT_NAME.to_string(), method.return_type.clone()));

            // Minimal env: self (concrete), result, params. Intentionally carries
            // NO trait-method metadata, so a clause invoking `self.m()` fails to
            // lower and is skipped — conservative, since conformance still checks
            // it and the caller simply doesn't gain that (harder) clause.
            let mut env = TypeEnv::new();
            env.insert(TRAIT_RECEIVER_NAME.to_string(), concrete_type.clone());
            env.insert(TRAIT_RESULT_NAME.to_string(), method.return_type.clone());
            for (param_name, param_ty) in &method.params {
                env.insert(param_name.clone(), param_ty.clone());
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

            let body =
                match self.encode_trait_expr_with_bindings(&ensured, &local_bindings, &local_types)
                {
                    Ok(term) => term,
                    Err(_) => continue,
                };
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

    fn encode_trait_expr_with_bindings(
        &mut self,
        expr: &TrustVcExpr,
        bindings: &[(&str, Term)],
        local_types: &[(String, TrustVcType)],
    ) -> TrustVcResult<Term> {
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

fn build_trait_contract_env(decl: &TraitDecl, method: &TraitMethodDecl) -> TypeEnv {
    let mut env = TypeEnv::new();
    env.insert(TRAIT_RECEIVER_NAME.to_string(), TrustVcType::Poly);
    env.insert(TRAIT_RESULT_NAME.to_string(), method.return_type.clone());
    for (param_name, param_ty) in &method.params {
        env.insert(param_name.clone(), param_ty.clone());
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
