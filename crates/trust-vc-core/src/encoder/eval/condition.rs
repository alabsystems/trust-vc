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
        if super::super::verification::test_hooks::take_forced_encode_condition_panic() {
            panic!("forced encode_condition_typed panic");
        }

        // Expand inline spec function calls before any further processing.
        // Inline functions have their body substituted at call sites instead
        // of using UF + body axiom. Part of #2488.
        let expr = if !self.state.inline_bodies.is_empty() {
            std::borrow::Cow::Owned(super::substitute_inline_calls(
                expr,
                &self.state.inline_bodies,
            ))
        } else {
            std::borrow::Cow::Borrowed(expr)
        };

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
        ast_parser.in_assumption_context = self.state.in_assumption_context;
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
        ast_parser
            .map_dom_bridges
            .clone_from(&self.state.map_dom_bridges);
        ast_parser
            .pure_collection_cache
            .clone_from(&self.state.pure_collection_cache);
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
        let expr = if !self.state.inline_bodies.is_empty() {
            std::borrow::Cow::Owned(super::substitute_inline_calls(
                expr,
                &self.state.inline_bodies,
            ))
        } else {
            std::borrow::Cow::Borrowed(expr)
        };

        let normalized = if !self.state.equality_assumptions.is_empty() {
            super::super::ir_encoder::normalize::substitute_and_normalize(
                &expr,
                &self.state.equality_assumptions,
            )
        } else {
            super::super::ir_encoder::normalize::normalize_int_expr(&expr)
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
        ast_parser.in_assumption_context = self.state.in_assumption_context;
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
        ast_parser
            .map_dom_bridges
            .clone_from(&self.state.map_dom_bridges);
        ast_parser
            .pure_collection_cache
            .clone_from(&self.state.pure_collection_cache);
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
        ast_parser.in_assumption_context = true;
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
        ast_parser
            .map_dom_bridges
            .clone_from(&self.state.map_dom_bridges);
        ast_parser
            .pure_collection_cache
            .clone_from(&self.state.pure_collection_cache);
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
        if super::super::verification::test_hooks::take_forced_encode_condition_panic() {
            panic!("forced encode_condition_typed panic");
        }

        // Expand inline spec-function calls before overflow-aware encoding, the
        // same way `encode_condition_typed`/`encode_refutation_condition_typed`
        // do. An `#[trust_vc::inline]` function is call-site-substituted and is
        // therefore NOT declared as a backend UF, so encoding an un-substituted
        // `f(args)` here would fail with "Undefined function: f". Part of #2777.
        let expr = if !self.state.inline_bodies.is_empty() {
            std::borrow::Cow::Owned(super::substitute_inline_calls(
                expr,
                &self.state.inline_bodies,
            ))
        } else {
            std::borrow::Cow::Borrowed(expr)
        };
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
        // Override derived div0/bitshift with context-propagated behaviors.
        ast_parser.div0_behavior = self.state.div0_behavior;
        ast_parser.bitshift_behavior = self.state.bitshift_behavior;
        ast_parser.function_return_types = Some(&self.fn_ctx.return_types);
        ast_parser.function_param_types = Some(&self.fn_ctx.param_types);
        ast_parser.function_type_params = Some(&self.fn_ctx.type_params);
        ast_parser.poly_context = Some(&mut self.registries.poly_context);
        ast_parser.ground_pool = Some(&mut self.state.ground_pool);
        ast_parser.choose_registry = Some(&mut self.registries.choose_registry);
        ast_parser.prophecy_registry = Some(&mut self.registries.prophecy_registry);
        ast_parser.in_assumption_context = self.state.in_assumption_context;
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
        ast_parser
            .map_dom_bridges
            .clone_from(&self.state.map_dom_bridges);
        ast_parser
            .pure_collection_cache
            .clone_from(&self.state.pure_collection_cache);
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
        let term = result?;
        let overflow_checks = ast_parser.take_overflow_checks();
        let const_fold_overflow = ast_parser.take_const_fold_overflow_verdicts();
        Ok((term, overflow_checks, const_fold_overflow))
    }
}
