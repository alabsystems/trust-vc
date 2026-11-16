// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Term;

use super::super::types::infer_int_width_from_types;
use super::super::{AYEncoder, AstExpressionParser};
use crate::error::{TrustVcError, TrustVcResult};
use crate::ir_lowering::lower_syn_expr;

impl AYEncoder {
    /// Infer the bit width for integer literals from AYEncoder's variable context.
    /// Cached per-encoder; invalidated when `declare_variable` adds new types.
    /// Part of #1786: avoids O(V) HashMap allocation per integer literal.
    pub(in super::super) fn infer_int_width(&self) -> u32 {
        if let Some(cached) = self.state.cached_int_width.get() {
            return cached;
        }
        let width = infer_int_width_from_types(self.var_types.values());
        self.state.cached_int_width.set(Some(width));
        width
    }

    /// Encodes a trigger expression string via typed lowering (fail-closed).
    ///
    /// Lowers the trigger string through `syn::parse_str` → `lower_syn_expr` →
    /// `encode_condition_typed`. Returns an error if any stage fails. No fallback
    /// to the legacy `parse_syn_expr` path — consistent with `resolve_condition`.
    /// Part of #1690: surface parse/lowering/encoding failures as `TrustVcError`.
    pub(in super::super) fn encode_trigger_expr_typed(
        &mut self,
        trigger: &crate::ir::TrustVcExpr,
    ) -> TrustVcResult<Term> {
        self.encode_condition_typed(trigger)
            .map_err(|e| TrustVcError::Encoding {
                context: "encode trigger",
                detail: format!("Failed to encode typed trigger expression: {}", e),
            })
    }

    /// Encodes a trigger expression string via typed lowering (fail-closed).
    ///
    /// Legacy compatibility wrapper around `encode_trigger_expr_typed`.
    pub(in super::super) fn encode_trigger_typed(&mut self, trigger: &str) -> TrustVcResult<Term> {
        let syn_expr: syn::Expr =
            syn::parse_str(trigger).map_err(|source| TrustVcError::Parse {
                context: "parse trigger",
                source,
            })?;

        // Borrow the cached lowering env instead of rebuilding per trigger.
        // The cache is kept synchronized at declare_variable and
        // register_function_context mutation points. Part of #2181.
        let lowered = lower_syn_expr(&syn_expr, &self.state.lowering_env).map_err(|source| {
            TrustVcError::Lowering {
                context: "lower trigger",
                source,
            }
        })?;
        self.encode_trigger_expr_typed(&lowered)
            .map_err(|e| TrustVcError::Encoding {
                context: "encode trigger",
                detail: format!("Failed to encode trigger '{}': {}", trigger, e),
            })
    }

    /// Refuse a root whose typing disagrees anywhere
    /// (`ir_lowering::validate_ir_typing`, design-trust-proof-backend.md §5b
    /// rule 13), so both frontends' IR passes the one validator.
    pub(in super::super) fn validate_ir_typing(
        &self,
        expr: &crate::ir::TrustVcExpr,
        locals: Option<&std::collections::HashMap<String, crate::ir::TrustVcType>>,
    ) -> TrustVcResult<()> {
        let scope = crate::ir_lowering::TypingScope {
            variables: Some(&self.var_types),
            locals,
            functions: Some(&self.fn_ctx.return_types),
            parameters: Some(&self.fn_ctx.param_types),
        };
        crate::ir_lowering::validate_ir_typing(expr, &scope).map_err(|detail| {
            TrustVcError::Encoding {
                context: "validate IR typing",
                detail,
            }
        })
    }

    /// The tree a root is ENCODED as: `expr` with every inline spec-function
    /// call replaced by its body (`substitute_inline_calls`), validated as a
    /// whole (§5b rule 13). The validator runs on the tree the encoder reads,
    /// so a claim inside an inline body — never itself encoded as an axiom —
    /// is checked where the body lands, at the argument types it lands at
    /// (with `s: Seq<u8>`, an inline body `p[0]` declared `i8` made `f(s) ==
    /// -56` `Verified` for `s[0] == 200`). The root as given is validated
    /// too: a call node that substitution replaces carries its own result
    /// claim.
    pub(in super::super) fn prepare_root<'e>(
        &self,
        expr: &'e crate::ir::TrustVcExpr,
    ) -> TrustVcResult<std::borrow::Cow<'e, crate::ir::TrustVcExpr>> {
        self.validate_ir_typing(expr, None)?;
        if self.state.inline_bodies.is_empty() {
            return Ok(std::borrow::Cow::Borrowed(expr));
        }
        let substituted = super::substitute_inline_calls(expr, &self.state.inline_bodies);
        self.validate_ir_typing(&substituted, None)?;
        Ok(std::borrow::Cow::Owned(substituted))
    }

    // encode_trust_vc_expr dispatch lives in encoder/ir_encoder/mod.rs (Part of #1865).

    /// Encodes a `TrustVcExpr` into a ay `Term` using the typed IR encoder.
    ///
    /// `TrustVcExpr -> AstExpressionParser::encode_trust_vc_expr -> Term`.
    /// The legacy string-based `parse_condition` path was removed in Phase 5
    /// Step 1 (#1866) — it had zero callers after the typed pipeline became
    /// fail-closed in #1927.
    ///
    /// Part of #1927: typed bridge for Phase 4-6 integration.
    /// Part of #1690: returns `TrustVcResult` — callers no longer need String wrapping.
    pub(in super::super) fn encode_condition_typed(
        &mut self,
        expr: &crate::ir::TrustVcExpr,
    ) -> TrustVcResult<Term> {
        #[cfg(test)]
        let _phase_observer =
            crate::encoder::verification::phase_observer::span("encode", "encode_condition");
        #[cfg(test)]
        if super::super::verification::test_hooks::take_forced_encode_condition_panic() {
            panic!("forced encode_condition_typed panic");
        }
        // Inline spec functions have their body substituted at call sites
        // instead of using UF + body axiom (#2488); the result is validated.
        let capture = self.state.scalar_cast_capture.clone();
        let _active_capture = capture.as_ref().and_then(|sink| sink.begin());
        let original_root = capture
            .as_ref()
            .map(|_| crate::scalar_cast_capture::typed_root(expr));
        let expr = self.prepare_root(expr)?;

        // Substitute assumed equalities and normalize arithmetic before encoding.
        // Equality bindings like `y == d * q2` are substituted into the
        // expression first, then commutative/associative normalization
        // canonicalizes the result. Applied to both assumptions and assertions
        // so ay sees structurally identical terms on both sides of the proof.
        // Part of #2187, #2400.
        let normalized = if !self.state.equality_assumptions.is_empty() {
            super::super::ir_encoder::normalize::substitute_and_normalize(
                &expr,
                &self.state.equality_assumptions,
            )
        } else {
            super::super::ir_encoder::normalize::normalize_int_expr(&expr)
        };
        let prepared_root = capture
            .as_ref()
            .map(|_| crate::scalar_cast_capture::typed_root(&normalized));
        let mut ast_parser = AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.fn_ctx.functions,
        );
        ast_parser.scalar_casts = capture.as_ref().map(|_| Vec::new());
        ast_parser.function_return_types = Some(&self.fn_ctx.return_types);
        ast_parser.function_param_types = Some(&self.fn_ctx.param_types);
        ast_parser.function_type_params = Some(&self.fn_ctx.type_params);
        ast_parser.seq_contains_quantified_memo = Some(&mut self.seq_contains_quantified_memo);
        ast_parser.poly_context = Some(&mut self.registries.poly_context);
        ast_parser.ground_pool = Some(&mut self.state.ground_pool);
        ast_parser.choose_registry = Some(&mut self.registries.choose_registry);
        ast_parser.prophecy_registry = Some(&mut self.registries.prophecy_registry);
        ast_parser.in_assumption_context = self.state.in_assumption_context;
        // An assumption encoded here DROPS the obligations it pushes (a spec
        // function's defining axiom, a broadcast, a ground re-encoding); so does
        // a demand-inline retry (rule 9).
        ast_parser.obligations_unchecked =
            self.state.demand_inlined_bodies || self.state.in_assumption_context;
        ast_parser.pending_universal_closure = self.state.pending_universal_closure;
        ast_parser.preserve_assumption_quantifier_sorts =
            self.state.preserve_assumption_quantifier_sorts;
        ast_parser.solver_mode = self.state.active_solver_mode;
        // Which collection lengths already carry an asserted `<= usize::MAX`
        // (exec `Vec`/slice/array only — see `assert_len_usize_bounded`). Read
        // by carrier-representability gates that hold a length `Term` but not
        // the `bounded_len` bit. EVERY parser built here must be seeded: two
        // encodings of the SAME proposition that disagree about boundedness
        // produce two different (and unrelated) length companions, which showed
        // up as a `Vec == Vec` pin regressing to a counterexample.
        ast_parser
            .usize_bounded_lens
            .clone_from(&self.state.usize_bounded_lens);
        // Seed the parser with persisted ground element aliases from prior
        // encoding rounds (assumptions → assertions). Part of #2680.
        #[cfg(feature = "native-seq")]
        {
            ast_parser
                .native_seq_ground_element_aliases
                .clone_from(&self.state.native_seq_ground_aliases);
        }
        ast_parser
            .nat_cast_aliases
            .clone_from(&self.state.nat_cast_aliases);
        ast_parser.map_subset_seen = self.state.map_subset_seen;
        ast_parser.seq_element_model_demanded = self.state.seq_element_model_demanded;
        ast_parser.demand_inline_overrides_active = self.state.demand_inline_overrides_active;
        ast_parser
            .map_dom_bridges
            .clone_from(&self.state.map_dom_bridges);
        ast_parser
            .pure_collection_cache
            .clone_from(&self.state.pure_collection_cache);
        ast_parser
            .projected_collection_meta
            .clone_from(&self.state.projected_collection_meta);
        let result = ast_parser.encode_trust_vc_expr(&normalized);
        self.state.diagnostics.merge(&ast_parser.diagnostics);
        // Persist any new ground element aliases back to encoder state.
        #[cfg(feature = "native-seq")]
        {
            self.state
                .native_seq_ground_aliases
                .extend(ast_parser.native_seq_ground_element_aliases.iter());
        }
        self.state
            .nat_cast_aliases
            .extend(ast_parser.nat_cast_aliases.iter());
        self.state.map_subset_seen |= ast_parser.map_subset_seen;
        self.state
            .map_dom_bridges
            .extend(ast_parser.map_dom_bridges.iter());
        self.state.pure_collection_cache.extend(
            ast_parser
                .pure_collection_cache
                .iter()
                .map(|(k, v)| (k.clone(), *v)),
        );
        self.state.projected_collection_meta.extend(
            ast_parser
                .projected_collection_meta
                .iter()
                .map(|(k, v)| (*k, v.clone())),
        );
        if let Ok(term) = &result {
            let checks = ast_parser.take_overflow_checks();
            let constants = ast_parser.take_const_fold_overflow_verdicts();
            record_cast_condition(
                capture,
                &mut ast_parser,
                crate::scalar_cast_capture::ScalarCastEncodingPhase::Condition,
                original_root.unwrap_or_else(|| Err("capture disabled".into())),
                prepared_root.unwrap_or_else(|| Err("capture disabled".into())),
                *term,
                &checks,
                &constants,
            );
        }
        result
    }

    /// Encodes the logical refutation of a `TrustVcExpr`.
    ///
    /// This mirrors `encode_condition_typed` setup, then lets the IR encoder
    /// push negation through supported boolean forms. In particular, a false
    /// universal assertion is encoded with fresh witness constants instead of
    /// a backend `exists` term.
    pub(in super::super) fn encode_refutation_condition_typed(
        &mut self,
        expr: &crate::ir::TrustVcExpr,
    ) -> TrustVcResult<Term> {
        #[cfg(test)]
        let _phase_observer =
            crate::encoder::verification::phase_observer::span("encode", "encode_refutation");
        let capture = self.state.scalar_cast_capture.clone();
        let _active_capture = capture.as_ref().and_then(|sink| sink.begin());
        let original_root = capture
            .as_ref()
            .map(|_| crate::scalar_cast_capture::typed_root(expr));
        let expr = self.prepare_root(expr)?;

        let normalized = if !self.state.equality_assumptions.is_empty() {
            super::super::ir_encoder::normalize::substitute_and_normalize(
                &expr,
                &self.state.equality_assumptions,
            )
        } else {
            super::super::ir_encoder::normalize::normalize_int_expr(&expr)
        };
        let prepared_root = capture
            .as_ref()
            .map(|_| crate::scalar_cast_capture::typed_root(&normalized));
        let mut ast_parser = AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.fn_ctx.functions,
        );
        ast_parser.scalar_casts = capture.as_ref().map(|_| Vec::new());
        ast_parser.function_return_types = Some(&self.fn_ctx.return_types);
        ast_parser.function_param_types = Some(&self.fn_ctx.param_types);
        ast_parser.function_type_params = Some(&self.fn_ctx.type_params);
        ast_parser.seq_contains_quantified_memo = Some(&mut self.seq_contains_quantified_memo);
        ast_parser.poly_context = Some(&mut self.registries.poly_context);
        ast_parser.ground_pool = Some(&mut self.state.ground_pool);
        ast_parser.choose_registry = Some(&mut self.registries.choose_registry);
        ast_parser.prophecy_registry = Some(&mut self.registries.prophecy_registry);
        ast_parser.in_assumption_context = self.state.in_assumption_context;
        ast_parser.obligations_unchecked =
            self.state.demand_inlined_bodies || self.state.in_assumption_context;
        ast_parser.pending_universal_closure = self.state.pending_universal_closure;
        ast_parser.preserve_assumption_quantifier_sorts =
            self.state.preserve_assumption_quantifier_sorts;
        ast_parser.solver_mode = self.state.active_solver_mode;
        // Length-boundedness view — see the note at the first parser site.
        ast_parser
            .usize_bounded_lens
            .clone_from(&self.state.usize_bounded_lens);
        #[cfg(feature = "native-seq")]
        {
            ast_parser
                .native_seq_ground_element_aliases
                .clone_from(&self.state.native_seq_ground_aliases);
        }
        ast_parser
            .nat_cast_aliases
            .clone_from(&self.state.nat_cast_aliases);
        ast_parser.map_subset_seen = self.state.map_subset_seen;
        ast_parser.seq_element_model_demanded = self.state.seq_element_model_demanded;
        ast_parser.demand_inline_overrides_active = self.state.demand_inline_overrides_active;
        ast_parser
            .map_dom_bridges
            .clone_from(&self.state.map_dom_bridges);
        ast_parser
            .pure_collection_cache
            .clone_from(&self.state.pure_collection_cache);
        ast_parser
            .projected_collection_meta
            .clone_from(&self.state.projected_collection_meta);
        let result = ast_parser.encode_refutation_expr(&normalized);
        self.state.diagnostics.merge(&ast_parser.diagnostics);
        #[cfg(feature = "native-seq")]
        {
            self.state
                .native_seq_ground_aliases
                .extend(ast_parser.native_seq_ground_element_aliases.iter());
        }
        self.state
            .nat_cast_aliases
            .extend(ast_parser.nat_cast_aliases.iter());
        self.state.map_subset_seen |= ast_parser.map_subset_seen;
        self.state
            .map_dom_bridges
            .extend(ast_parser.map_dom_bridges.iter());
        self.state.pure_collection_cache.extend(
            ast_parser
                .pure_collection_cache
                .iter()
                .map(|(k, v)| (k.clone(), *v)),
        );
        self.state.projected_collection_meta.extend(
            ast_parser
                .projected_collection_meta
                .iter()
                .map(|(k, v)| (*k, v.clone())),
        );
        if let Ok(term) = &result {
            let checks = ast_parser.take_overflow_checks();
            let constants = ast_parser.take_const_fold_overflow_verdicts();
            record_cast_condition(
                capture,
                &mut ast_parser,
                crate::scalar_cast_capture::ScalarCastEncodingPhase::Refutation,
                original_root.unwrap_or_else(|| Err("capture disabled".into())),
                prepared_root.unwrap_or_else(|| Err("capture disabled".into())),
                *term,
                &checks,
                &constants,
            );
        }
        result
    }

    /// Encodes a `TrustVcExpr` directly to a ay `Term` (no thread-local lookup).
    pub(in super::super) fn resolve_condition_typed(
        &mut self,
        expr: &crate::ir::TrustVcExpr,
    ) -> TrustVcResult<Term> {
        self.encode_condition_typed(expr)
    }

    /// Encodes the logical refutation of a `TrustVcExpr` directly to a ay `Term`.
    pub(in super::super) fn resolve_refutation_condition_typed(
        &mut self,
        expr: &crate::ir::TrustVcExpr,
    ) -> TrustVcResult<Term> {
        self.encode_refutation_condition_typed(expr)
    }

    pub(in super::super) fn resolve_condition_typed_with_bindings(
        &mut self,
        expr: &crate::ir::TrustVcExpr,
        bindings: &[(&str, Term)],
    ) -> TrustVcResult<Term> {
        if let Some(capture) = &self.state.scalar_cast_capture {
            capture.refuse("cast binding does not cover an alternate local-binding encoder");
        }
        self.validate_ir_typing(expr, None)?;
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
        ast_parser.seq_contains_quantified_memo = Some(&mut self.seq_contains_quantified_memo);
        ast_parser.poly_context = Some(&mut self.registries.poly_context);
        ast_parser.ground_pool = Some(&mut self.state.ground_pool);
        ast_parser.in_assumption_context = true;
        ast_parser.obligations_unchecked = true;
        ast_parser.pending_universal_closure = self.state.pending_universal_closure;
        ast_parser.preserve_assumption_quantifier_sorts =
            self.state.preserve_assumption_quantifier_sorts;
        ast_parser.solver_mode = self.state.active_solver_mode;
        // Length-boundedness view — see the note at the first parser site.
        ast_parser
            .usize_bounded_lens
            .clone_from(&self.state.usize_bounded_lens);
        #[cfg(feature = "native-seq")]
        {
            ast_parser
                .native_seq_ground_element_aliases
                .clone_from(&self.state.native_seq_ground_aliases);
        }
        ast_parser
            .nat_cast_aliases
            .clone_from(&self.state.nat_cast_aliases);
        ast_parser.map_subset_seen = self.state.map_subset_seen;
        ast_parser.seq_element_model_demanded = self.state.seq_element_model_demanded;
        ast_parser.demand_inline_overrides_active = self.state.demand_inline_overrides_active;
        ast_parser
            .map_dom_bridges
            .clone_from(&self.state.map_dom_bridges);
        ast_parser
            .pure_collection_cache
            .clone_from(&self.state.pure_collection_cache);
        ast_parser
            .projected_collection_meta
            .clone_from(&self.state.projected_collection_meta);
        for (name, term) in bindings {
            let ty = self
                .var_types
                .get(*name)
                .cloned()
                .ok_or_else(|| TrustVcError::Internal {
                    context: "resolve typed condition with bindings",
                    detail: format!("Missing type for bound variable '{}'", name),
                })?;
            ast_parser.local_vars.insert((*name).to_string(), *term);
            ast_parser.local_var_types.insert((*name).to_string(), ty);
        }
        let result = ast_parser.encode_trust_vc_expr(expr);
        self.state.diagnostics.merge(&ast_parser.diagnostics);
        #[cfg(feature = "native-seq")]
        {
            self.state
                .native_seq_ground_aliases
                .extend(ast_parser.native_seq_ground_element_aliases.iter());
        }
        self.state
            .nat_cast_aliases
            .extend(ast_parser.nat_cast_aliases.iter());
        self.state.map_subset_seen |= ast_parser.map_subset_seen;
        self.state
            .map_dom_bridges
            .extend(ast_parser.map_dom_bridges.iter());
        self.state.pure_collection_cache.extend(
            ast_parser
                .pure_collection_cache
                .iter()
                .map(|(k, v)| (k.clone(), *v)),
        );
        self.state.projected_collection_meta.extend(
            ast_parser
                .projected_collection_meta
                .iter()
                .map(|(k, v)| (*k, v.clone())),
        );
        result
    }

    /// Encodes a `TrustVcExpr` AND collects overflow checks (no thread-local lookup).
    ///
    /// Typed-pipeline equivalent of `resolve_condition_with_overflow()`. Part of #2219.
    /// Uses the encoder's stored `div0_behavior` and `bitshift_behavior` from the
    /// `VerificationContext` rather than deriving from the `check_overflow` boolean.
    /// This ensures spec/proof mode correctly suppresses div-by-zero and shift
    /// bounds checks. Part of #2516.
    pub(in super::super) fn resolve_condition_with_overflow_typed(
        &mut self,
        expr: &crate::ir::TrustVcExpr,
        check_overflow: bool,
    ) -> TrustVcResult<(Term, Vec<super::super::parser_state::OverflowCheck>)> {
        let (term, checks, _const_fold) =
            self.resolve_condition_overflow_with_const_fold(expr, check_overflow)?;
        Ok((term, checks))
    }

    /// Like [`Self::resolve_condition_with_overflow_typed`], but also returns the
    /// constant-folded definite overflow verdicts collected during encoding.
    ///
    /// Each verdict is a `(label, overflows)` pair for an all-constant
    /// fixed-width arithmetic operation; `overflows == true` is a definite
    /// counterexample. Used by `check_overflow_predicates` so that fully-ground
    /// overflow queries (e.g. `255u8 + 1u8`) yield a definite verdict instead of
    /// the solver's SAT-with-empty-model CEGQI artifact (#2778).
    pub(in super::super) fn resolve_condition_overflow_with_const_fold(
        &mut self,
        expr: &crate::ir::TrustVcExpr,
        check_overflow: bool,
    ) -> TrustVcResult<(
        Term,
        Vec<super::super::parser_state::OverflowCheck>,
        Vec<super::super::parser_state::ConstFoldOverflowCheck>,
    )> {
        #[cfg(test)]
        let _phase_observer = crate::encoder::verification::phase_observer::span(
            "encode",
            "encode_bounds_and_overflow",
        );
        #[cfg(test)]
        if super::super::verification::test_hooks::take_forced_encode_condition_panic() {
            panic!("forced encode_condition_typed panic");
        }
        // Inline spec-function calls are expanded before overflow-aware
        // encoding too: an `#[trust_vc::inline]` function is not declared as a
        // backend UF, so an un-substituted `f(args)` would fail with
        // "Undefined function: f" (#2777).
        let capture = self.state.scalar_cast_capture.clone();
        let _active_capture = capture.as_ref().and_then(|sink| sink.begin());
        let original_root = capture
            .as_ref()
            .map(|_| crate::scalar_cast_capture::typed_root(expr));
        let expr = self.prepare_root(expr)?;
        let prepared_root = capture
            .as_ref()
            .map(|_| crate::scalar_cast_capture::typed_root(&expr));
        let expr: &crate::ir::TrustVcExpr = &expr;

        let overflow_behavior = if check_overflow {
            crate::vc::OverflowBehavior::Error
        } else {
            crate::vc::OverflowBehavior::default_no_check()
        };
        let mut ast_parser = AstExpressionParser::with_overflow_behavior(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.fn_ctx.functions,
            overflow_behavior,
        );
        ast_parser.scalar_casts = capture.as_ref().map(|_| Vec::new());
        // Override derived div0/bitshift with context-propagated behaviors.
        ast_parser.div0_behavior = self.state.div0_behavior;
        ast_parser.bitshift_behavior = self.state.bitshift_behavior;
        ast_parser.function_return_types = Some(&self.fn_ctx.return_types);
        ast_parser.function_param_types = Some(&self.fn_ctx.param_types);
        ast_parser.function_type_params = Some(&self.fn_ctx.type_params);
        ast_parser.seq_contains_quantified_memo = Some(&mut self.seq_contains_quantified_memo);
        ast_parser.poly_context = Some(&mut self.registries.poly_context);
        ast_parser.ground_pool = Some(&mut self.state.ground_pool);
        ast_parser.choose_registry = Some(&mut self.registries.choose_registry);
        ast_parser.prophecy_registry = Some(&mut self.registries.prophecy_registry);
        ast_parser.in_assumption_context = self.state.in_assumption_context;
        // The obligations are returned to the caller, which checks them.
        ast_parser.obligations_unchecked = self.state.demand_inlined_bodies;
        ast_parser.pending_universal_closure = self.state.pending_universal_closure;
        // Assumption path only: eager-Skolemize a top-level positive assumption
        // existential (never threaded into the refutation/goal path, so a
        // goal-position existential is structurally never Skolemized).
        ast_parser.skolemize_top_level_assumption_exists =
            self.state.skolemize_top_level_assumption_exists;
        ast_parser.preserve_assumption_quantifier_sorts =
            self.state.preserve_assumption_quantifier_sorts;
        ast_parser.solver_mode = self.state.active_solver_mode;
        // Length-boundedness view — see the note at the first parser site.
        ast_parser
            .usize_bounded_lens
            .clone_from(&self.state.usize_bounded_lens);
        #[cfg(feature = "native-seq")]
        {
            ast_parser
                .native_seq_ground_element_aliases
                .clone_from(&self.state.native_seq_ground_aliases);
        }
        ast_parser
            .nat_cast_aliases
            .clone_from(&self.state.nat_cast_aliases);
        ast_parser.map_subset_seen = self.state.map_subset_seen;
        ast_parser.seq_element_model_demanded = self.state.seq_element_model_demanded;
        ast_parser.demand_inline_overrides_active = self.state.demand_inline_overrides_active;
        ast_parser
            .map_dom_bridges
            .clone_from(&self.state.map_dom_bridges);
        ast_parser
            .pure_collection_cache
            .clone_from(&self.state.pure_collection_cache);
        ast_parser
            .projected_collection_meta
            .clone_from(&self.state.projected_collection_meta);
        let result = ast_parser.encode_trust_vc_expr(expr);
        self.state.diagnostics.merge(&ast_parser.diagnostics);
        #[cfg(feature = "native-seq")]
        {
            self.state
                .native_seq_ground_aliases
                .extend(ast_parser.native_seq_ground_element_aliases.iter());
        }
        self.state
            .nat_cast_aliases
            .extend(ast_parser.nat_cast_aliases.iter());
        self.state.map_subset_seen |= ast_parser.map_subset_seen;
        self.state
            .map_dom_bridges
            .extend(ast_parser.map_dom_bridges.iter());
        self.state.pure_collection_cache.extend(
            ast_parser
                .pure_collection_cache
                .iter()
                .map(|(k, v)| (k.clone(), *v)),
        );
        self.state.projected_collection_meta.extend(
            ast_parser
                .projected_collection_meta
                .iter()
                .map(|(k, v)| (*k, v.clone())),
        );
        let term = result?;
        let overflow_checks = ast_parser.take_overflow_checks();
        let const_fold_overflow = ast_parser.take_const_fold_overflow_verdicts();
        record_cast_condition(
            capture,
            &mut ast_parser,
            crate::scalar_cast_capture::ScalarCastEncodingPhase::CheckedCondition,
            original_root.unwrap_or_else(|| Err("capture disabled".into())),
            prepared_root.unwrap_or_else(|| Err("capture disabled".into())),
            term,
            &overflow_checks,
            &const_fold_overflow,
        );
        Ok((term, overflow_checks, const_fold_overflow))
    }
}

fn record_cast_condition(
    capture: Option<crate::scalar_cast_capture::ScalarCastCapture>,
    parser: &mut AstExpressionParser<'_>,
    phase: crate::scalar_cast_capture::ScalarCastEncodingPhase,
    original_root: Result<crate::ir::TrustVcExpr, String>,
    prepared_root: Result<crate::ir::TrustVcExpr, String>,
    term: Term,
    overflow_checks: &[super::super::parser_state::OverflowCheck],
    const_fold_overflow: &[super::super::parser_state::ConstFoldOverflowCheck],
) {
    if let Some(capture) = capture {
        let observation = (|| {
            if let Some(reason) = parser.scalar_cast_refusal.take() {
                return Err(reason);
            }
            let result_term = crate::scalar_cast_capture::actual_term(parser.solver, term)?;
            let domain_checks = overflow_checks
                .iter()
                .map(|(label, predicate)| {
                    let predicate =
                        crate::scalar_cast_capture::actual_term(parser.solver, *predicate)?;
                    if predicate.sort != ay_dpll::api::Sort::Bool {
                        return Err("cast domain predicate is not Bool".into());
                    }
                    Ok(crate::scalar_cast_capture::ScalarCastDomainCheck {
                        label: label.to_string(),
                        predicate: predicate.text,
                        bindings: predicate.bindings,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            Ok(crate::scalar_cast_capture::ScalarCastCondition {
                phase,
                original_typed_root: original_root?,
                prepared_typed_root: prepared_root?,
                result_sort: result_term.sort,
                result_bindings: result_term.bindings,
                result_term: result_term.text,
                casts: parser.scalar_casts.take().expect("capture enabled"),
                domain_checks,
                constant_overflow_verdicts: const_fold_overflow
                    .iter()
                    .map(|(label, value)| (label.to_string(), *value))
                    .collect(),
            })
        })();
        match observation {
            Ok(row) => capture.record(row),
            Err(reason) => capture.refuse(reason),
        }
    }
}
