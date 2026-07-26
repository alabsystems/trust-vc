// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{ArraySort, Sort};

use super::super::types::sort_for_type;
use super::super::AYEncoder;
use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::TrustVcType;
use crate::vc::FunctionContext;

impl AYEncoder {
    pub(in super::super) fn collection_constructor_is_empty(name: &str) -> bool {
        name.starts_with(crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX)
            && (name.ends_with("_empty") || name.ends_with("_new"))
    }

    pub(in super::super) fn register_zero_arity_collection_metadata(
        &mut self,
        name: &str,
        term: ay_dpll::api::Term,
        return_ty: &crate::ir::TrustVcType,
    ) -> TrustVcResult<()> {
        let is_empty = Self::collection_constructor_is_empty(name);

        if return_ty.has_collection_length() {
            #[cfg(feature = "native-strings")]
            if return_ty.is_string_like() {
                let str_len_raw =
                    self.solver
                        .try_str_len(term)
                        .map_err(|e| TrustVcError::Encoding {
                            context: "register function context",
                            detail: format!(
                                "Failed to compute str.len for native string func '{}': {e}",
                                name
                            ),
                        })?;
                let int_len = self
                    .solver
                    .declare_const(&format!("__native_string_len_{name}"), Sort::Int);
                let len_bridge = self.solver.try_eq(int_len, str_len_raw).map_err(|e| {
                    TrustVcError::Encoding {
                        context: "register function context",
                        detail: format!("Failed to create str.len bridge for func '{}': {e}", name),
                    }
                })?;
                self.solver
                    .try_assert_term(len_bridge)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "register function context",
                        detail: format!("Failed to assert str.len bridge for func '{}': {e}", name),
                    })?;
                let zero = self.solver.int_const(0);
                let len_nonneg =
                    self.solver
                        .try_ge(int_len, zero)
                        .map_err(|e| TrustVcError::Encoding {
                            context: "register function context",
                            detail: format!(
                                "Failed to create native string len >= 0 for func '{}': {e}",
                                name
                            ),
                        })?;
                self.solver
                    .try_assert_term(len_nonneg)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "register function context",
                        detail: format!(
                            "Failed to assert native string len >= 0 for func '{}': {e}",
                            name
                        ),
                    })?;
                self.collection_lengths.insert(name.to_string(), int_len);
                if is_empty {
                    let zero = self.solver.int_const(0);
                    let empty_len =
                        self.solver
                            .try_eq(int_len, zero)
                            .map_err(|e| TrustVcError::Encoding {
                                context: "register function context",
                                detail: format!(
                                    "Failed to build empty native string length for '{name}': {e}",
                                ),
                            })?;
                    self.solver
                        .try_assert_term(empty_len)
                        .map_err(|e| TrustVcError::Encoding {
                            context: "register function context",
                            detail: format!(
                                "Failed to assert empty native string length for '{name}': {e}",
                            ),
                        })?;
                }
                return Ok(());
            }

            // Route A (#2779): spec-collection LENGTH is an unbounded Int
            // (matches the `declare_variable` root site at mod.rs), so the
            // "... length no overflow" obligations vanish soundly and symbolic
            // length/concat properties on function returns verify.
            //
            // F3 (point-interval): an EMPTY collection constructor's length
            // IS the literal 0. Registering the Int constant — instead of a
            // declared `__trust_vc_len_*` var anchored by `>= 0` and pinned
            // by `= 0` — makes every downstream consumer (push chains, ext-eq
            // range guards) constant-fold, and leaves no residual ground Int
            // atom pair (`<= 0 len` / `= 1 (+ len 1)`) to trip ay's
            // quantifier lane (the F6-class poison; see
            // docs/probes/2026-07-18-ay-lane/dump-smt2/RESULTS.txt).
            let declared_len = if is_empty {
                self.solver.int_const(0)
            } else {
                let len_name = format!("__trust_vc_len_{name}");
                let declared_len = self.solver.declare_const(&len_name, Sort::Int);
                let zero_len = self.solver.int_const(0);
                let len_nonneg = self.solver.try_ge(declared_len, zero_len).map_err(|e| {
                    TrustVcError::Encoding {
                        context: "register function context",
                        detail: format!("Failed to create length >= 0 for func '{name}': {e}"),
                    }
                })?;
                self.solver
                    .try_assert_term(len_nonneg)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "register function context",
                        detail: format!("Failed to assert length >= 0 for func '{name}': {e}"),
                    })?;
                declared_len
            };
            self.collection_lengths
                .insert(name.to_string(), declared_len);
            if let crate::ir::TrustVcType::Array(_, array_len) = return_ty {
                self.assert_fixed_array_int_length(name, declared_len, *array_len)?;
            }

            // Under native-seq, String/StrSlice/Seq<char> use Sort::Seq(BV(32))
            // and need seq.nth-based unicode invariant, not array select.
            // Create an Int-sorted seq.len alias for the invariant.
            #[cfg(feature = "native-seq")]
            {
                #[cfg(feature = "native-strings")]
                let is_native_char_seq = matches!(
                    return_ty,
                    crate::ir::TrustVcType::Seq(elem)
                        if matches!(elem.as_ref(), crate::ir::TrustVcType::Char)
                ) || matches!(
                    return_ty,
                    crate::ir::TrustVcType::Array(elem, _)
                        if matches!(elem.as_ref(), crate::ir::TrustVcType::Char)
                );
                #[cfg(not(feature = "native-strings"))]
                let is_native_char_seq = return_ty.is_string_like()
                    || matches!(
                        return_ty,
                        crate::ir::TrustVcType::Seq(elem)
                            if matches!(elem.as_ref(), crate::ir::TrustVcType::Char)
                    )
                    || matches!(
                        return_ty,
                        crate::ir::TrustVcType::Array(elem, _)
                            if matches!(elem.as_ref(), crate::ir::TrustVcType::Char)
                    );
                if is_native_char_seq {
                    let seq_len_raw =
                        self.solver
                            .try_seq_len(term)
                            .map_err(|e| TrustVcError::Encoding {
                                context: "register function context",
                                detail: format!(
                                    "Failed to compute seq.len for native-seq func '{}': {e}",
                                    name
                                ),
                            })?;
                    let int_len = self.solver.declare_const(
                        &format!("__native_seq_len_{name}"),
                        ay_dpll::api::Sort::Int,
                    );
                    let len_bridge = self.solver.try_eq(int_len, seq_len_raw).map_err(|e| {
                        TrustVcError::Encoding {
                            context: "register function context",
                            detail: format!(
                                "Failed to create seq.len bridge for func '{}': {e}",
                                name
                            ),
                        }
                    })?;
                    self.solver.try_assert_term(len_bridge).map_err(|e| {
                        TrustVcError::Encoding {
                            context: "register function context",
                            detail: format!(
                                "Failed to assert seq.len bridge for func '{}': {e}",
                                name
                            ),
                        }
                    })?;
                    self.assert_valid_char_sequence_native_seq(term, int_len)?;
                }
            }
            #[cfg(not(feature = "native-seq"))]
            {
                if matches!(
                    return_ty,
                    crate::ir::TrustVcType::String | crate::ir::TrustVcType::StrSlice
                ) || matches!(
                    return_ty,
                    crate::ir::TrustVcType::Seq(elem)
                        if matches!(elem.as_ref(), crate::ir::TrustVcType::Char)
                ) || matches!(
                    return_ty,
                    crate::ir::TrustVcType::Array(elem, _)
                        if matches!(elem.as_ref(), crate::ir::TrustVcType::Char)
                ) {
                    self.assert_valid_char_sequence(term, declared_len)?;
                }
            }
        }

        // Empty Set: constrain underlying boolean array to all-false so that
        // `Set::empty().contains(x)` is always false. Without this, the SMT
        // array is unconstrained and membership queries return arbitrary
        // values, causing false counterexamples. Fixes #2530.
        if is_empty {
            if let crate::ir::TrustVcType::Set(elem_ty) = return_ty {
                let false_val = self.solver.bool_const(false);
                let all_false = self
                    .solver
                    .try_const_array(sort_for_type(elem_ty), false_val)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "empty set array constraint",
                        detail: format!(
                            "Failed to create const_array(false) for empty set '{name}': {e}"
                        ),
                    })?;
                let eq =
                    self.solver
                        .try_eq(term, all_false)
                        .map_err(|e| TrustVcError::Encoding {
                            context: "empty set array constraint",
                            detail: format!(
                                "Failed to assert empty set array equality for '{name}': {e}"
                            ),
                        })?;
                self.solver
                    .try_assert_term(eq)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "empty set array constraint",
                        detail: format!("Failed to assert empty set constraint for '{name}': {e}"),
                    })?;
            }

            // Empty Multiset: constrain underlying count array to all-zero so that
            // `Multiset::empty().count(x)` is always 0. Without this, the SMT
            // array is unconstrained and count queries return arbitrary values.
            // Fixes #2604.
            if let crate::ir::TrustVcType::Multiset(elem_ty) = return_ty {
                let zero_count = self.solver.int_const(0);
                let all_zero = self
                    .solver
                    .try_const_array(sort_for_type(elem_ty), zero_count)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "empty multiset array constraint",
                        detail: format!(
                            "Failed to create const_array(0) for empty multiset '{name}': {e}"
                        ),
                    })?;
                let eq =
                    self.solver
                        .try_eq(term, all_zero)
                        .map_err(|e| TrustVcError::Encoding {
                            context: "empty multiset array constraint",
                            detail: format!(
                                "Failed to assert empty multiset array equality for '{name}': {e}"
                            ),
                        })?;
                self.solver
                    .try_assert_term(eq)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "empty multiset array constraint",
                        detail: format!(
                            "Failed to assert empty multiset constraint for '{name}': {e}"
                        ),
                    })?;
            }
        }

        if let crate::ir::TrustVcType::Map(key_ty, _) = return_ty {
            let dom_sort = Sort::Array(Box::new(ArraySort {
                index_sort: sort_for_type(key_ty),
                element_sort: Sort::Bool,
            }));
            let dom_name = format!("{name}_dom");
            let declared_dom = self.solver.declare_const(&dom_name, dom_sort);
            self.variables.insert(dom_name.clone(), declared_dom);

            // Empty Map: constrain domain array to all-false so that
            // `Map::empty().contains_key(k)` is always false. Fixes #2530.
            if is_empty {
                let false_val = self.solver.bool_const(false);
                let all_false = self
                    .solver
                    .try_const_array(sort_for_type(key_ty), false_val)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "empty map domain constraint",
                        detail: format!(
                            "Failed to create const_array(false) for empty map '{name}': {e}"
                        ),
                    })?;
                let eq = self.solver.try_eq(declared_dom, all_false).map_err(|e| {
                    TrustVcError::Encoding {
                        context: "empty map domain constraint",
                        detail: format!(
                            "Failed to assert empty map domain equality for '{name}': {e}"
                        ),
                    }
                })?;
                self.solver
                    .try_assert_term(eq)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "empty map domain constraint",
                        detail: format!("Failed to assert empty map domain for '{name}': {e}"),
                    })?;
            }
        }

        Ok(())
    }

    /// Registers a function context as an uninterpreted function in ay.
    ///
    /// For recursive functions, declares an uninterpreted function with proper
    /// arity so that `f(1)` and `f(2)` produce distinct ay terms. For
    /// non-recursive functions, also registers them (they may appear in
    /// postcondition reasoning).
    ///
    /// Part of #1690: returns `TrustVcResult` instead of `Result<(), String>`.
    pub(in super::super) fn register_function_context(
        &mut self,
        func_ctx: &FunctionContext,
    ) -> TrustVcResult<()> {
        let return_ty = self.record_function_context_metadata(func_ctx)?;
        let return_sort = sort_for_type(&return_ty);

        if func_ctx.params.is_empty() {
            // Zero-arity function: declare as a constant (equivalent to declare-fun with no args)
            let func_term = self.solver.declare_const(&func_ctx.name, return_sort);
            self.variables.insert(func_ctx.name.clone(), func_term);
            self.var_types
                .insert(func_ctx.name.clone(), return_ty.clone());
            if matches!(return_ty, TrustVcType::Unit) {
                super::super::unit::assert_unit_term(
                    &mut self.solver,
                    func_term,
                    "register function context",
                    &func_ctx.name,
                )?;
            }
            // Mirror into lowering_env variable namespace so trigger lowering
            // sees the constant (matches dual-visibility behavior). Part of #2181.
            self.state
                .lowering_env
                .insert(func_ctx.name.clone(), return_ty.clone());
            self.register_zero_arity_collection_metadata(&func_ctx.name, func_term, &return_ty)?;
        } else {
            // N-arity function: declare as an uninterpreted function
            let domain_sorts = func_ctx
                .params
                .iter()
                .map(|(_, param_type)| sort_for_type(param_type))
                .collect::<Vec<_>>();

            let func_decl = self
                .solver
                .try_declare_fun(&func_ctx.name, &domain_sorts, return_sort)
                .map_err(|e| TrustVcError::Encoding {
                    context: "register function context",
                    detail: format!("Failed to declare function '{}': {}", func_ctx.name, e),
                })?;

            self.fn_ctx
                .functions
                .insert(func_ctx.name.clone(), func_decl);
        }
        Ok(())
    }

    /// Records function signature metadata without declaring a ay symbol.
    ///
    /// Inline spec functions substitute their body before solver encoding, so
    /// they still need return/parameter metadata but must not appear as UFs.
    /// Part of #2488.
    pub(in super::super) fn register_function_context_metadata_only(
        &mut self,
        func_ctx: &FunctionContext,
    ) -> TrustVcResult<()> {
        self.record_function_context_metadata(func_ctx)?;
        Ok(())
    }

    fn record_function_context_metadata(
        &mut self,
        func_ctx: &FunctionContext,
    ) -> TrustVcResult<crate::ir::TrustVcType> {
        let return_ty = func_ctx.return_type.clone();
        // Reject any return type containing Opaque (top-level or nested).
        // Nested opaques (e.g., Seq<String>) previously only tracked diagnostics
        // but proceeded to encode the inner Opaque as Sort::Int — unsound (#1926).
        if return_ty.contains_opaque() {
            return Err(TrustVcError::Encoding {
                context: "register function context",
                detail: format!(
                    "Unsupported return type for function '{}': {} (contains unrecognized type)",
                    func_ctx.name,
                    return_ty.to_type_string()
                ),
            });
        }
        for (param_name, param_type) in &func_ctx.params {
            // Reject params containing Opaque types (#1925).
            // Closes the nested-opaque param gap that solver sort translation missed.
            if param_type.contains_opaque() {
                return Err(TrustVcError::Encoding {
                    context: "register function context",
                    detail: format!(
                        "Unsupported param type for '{}' in function '{}': {}",
                        param_name,
                        func_ctx.name,
                        param_type.to_type_string()
                    ),
                });
            }
        }
        self.fn_ctx
            .return_types
            .insert(func_ctx.name.clone(), return_ty.clone());
        // Store param types and infer type param names for polymorphic
        // call-site Box/Unbox wrapping. Part of #2053.
        let param_types: Vec<crate::ir::TrustVcType> =
            func_ctx.params.iter().map(|(_, ty)| ty.clone()).collect();
        let mut type_param_names = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for (_, ty) in &func_ctx.params {
            if let crate::ir::TrustVcType::TypeParam(name) = ty {
                if seen.insert(name.clone()) {
                    type_param_names.push(name.clone());
                }
            }
        }
        if let crate::ir::TrustVcType::TypeParam(name) = &return_ty {
            if seen.insert(name.clone()) {
                type_param_names.push(name.clone());
            }
        }
        self.fn_ctx
            .param_types
            .insert(func_ctx.name.clone(), param_types);
        if !type_param_names.is_empty() {
            self.fn_ctx
                .type_params
                .insert(func_ctx.name.clone(), type_param_names);
        }
        // Mirror into lowering_env function namespace so trigger lowering
        // sees function return types without a per-call rebuild. Part of #2181.
        self.state
            .lowering_env
            .insert_fn(func_ctx.name.clone(), return_ty.clone());
        Ok(return_ty)
    }
}
