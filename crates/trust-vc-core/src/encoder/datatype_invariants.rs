//! Datatype well-foundedness and type invariant encoding.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{FuncDecl, Sort, Term};

use super::{datatype_error, sanitize_symbol, DatatypeEncoding};
use crate::encoder::AYEncoder;
use crate::error::TrustVcResult;
use crate::ir::DatatypeVariant;

impl AYEncoder {
    /// Emits well-foundedness axioms for recursive datatypes.
    ///
    /// Declares a `dt_size` UF (`{name}__size : Int -> Int`) and asserts:
    /// - Base case: non-recursive constructors have size 0
    /// - Recursive case: `size(Cons(h, t)) == 1 + size(t)` (sum over recursive children)
    /// - Non-negativity: `forall x. {dt_size(x)} dt_size(x) >= 0`
    ///
    /// Skips silently for non-recursive datatypes (e.g., Option, Result).
    /// Part of #2421 Slice 4.
    pub(super) fn assert_well_foundedness(
        &mut self,
        datatype_name: &str,
        encoding: &DatatypeEncoding,
        variants: &[DatatypeVariant],
    ) -> TrustVcResult<()> {
        // Detect recursion: any field with RecursiveRef pointing to this datatype
        let has_recursive_field = variants.iter().any(|v| {
            v.fields.iter().any(|(_, ty)| {
                matches!(ty, crate::ir::TrustVcType::RecursiveRef(ref name) if name == datatype_name)
            })
        });
        if !has_recursive_field {
            return Ok(());
        }

        // Declare dt_size UF: {Datatype} -> Int over the native carrier sort
        // (was Int -> Int; constructor values are now carrier-sorted).
        let carrier_sort = super::datatype_carrier_sort(datatype_name);
        let size_name = format!("{}__size", encoding.symbol_prefix);
        let size_func = self
            .solver
            .try_declare_fun(&size_name, std::slice::from_ref(&carrier_sort), Sort::Int)
            .map_err(|err| {
                datatype_error(format!(
                    "Failed to declare size function '{}' for '{}': {}",
                    size_name, datatype_name, err
                ))
            })?;

        let zero = self.solver.int_const(0);
        let one = self.solver.int_const(1);

        // Per-variant size axioms using constructor-based triggers:
        //   forall fields. {Constructor(fields)} size(Constructor(fields)) == expected
        // For nullary base cases, assert as ground fact.
        for (variant, variant_encoding) in variants.iter().zip(encoding.variants.iter()) {
            let bound_vars =
                self.fresh_field_vars(&encoding.symbol_prefix, &variant.name, "wf", variant);
            let constructor_value =
                self.apply_constructor(&variant_encoding.constructor, &bound_vars)?;
            let size_of_constructor = self
                .solver
                .try_apply(&size_func, &[constructor_value])
                .map_err(|err| {
                    datatype_error(format!(
                        "Failed to apply size function for '{}::{}': {}",
                        datatype_name, variant.name, err
                    ))
                })?;

            // Collect size terms for recursive children
            let recursive_child_sizes: Vec<Term> = variant
                .fields
                .iter()
                .zip(bound_vars.iter())
                .filter_map(|((_, ty), term)| {
                    if matches!(ty, crate::ir::TrustVcType::RecursiveRef(ref name) if name == datatype_name)
                    {
                        self.solver.try_apply(&size_func, &[*term]).ok()
                    } else {
                        None
                    }
                })
                .collect();

            // Expected size: 0 for base cases, 1 + sum(child sizes) for recursive
            let expected_size = if recursive_child_sizes.is_empty() {
                zero
            } else {
                let mut sum = one;
                for child_size in &recursive_child_sizes {
                    sum = self.solver.try_add(sum, *child_size).map_err(|err| {
                        datatype_error(format!(
                            "Failed to add child size for '{}::{}': {}",
                            datatype_name, variant.name, err
                        ))
                    })?;
                }
                sum
            };

            let eq = self
                .solver
                .try_eq(size_of_constructor, expected_size)
                .map_err(|err| {
                    datatype_error(format!(
                        "Failed to build size equality for '{}::{}': {}",
                        datatype_name, variant.name, err
                    ))
                })?;

            if bound_vars.is_empty() {
                // Nullary constructor (base case): assert ground fact
                self.assert_axiom(
                    eq,
                    format!(
                        "Failed to assert size axiom for '{}::{}'",
                        datatype_name, variant.name
                    ),
                )?;
            } else {
                let trigger_groups = [vec![constructor_value]];
                let trigger_refs: Vec<&[Term]> = trigger_groups.iter().map(Vec::as_slice).collect();
                let quantified = self
                    .solver
                    .try_forall_with_triggers(&bound_vars, eq, &trigger_refs)
                    .map_err(|err| {
                        datatype_error(format!(
                            "Failed to quantify size axiom for '{}::{}': {}",
                            datatype_name, variant.name, err
                        ))
                    })?;
                self.assert_axiom(
                    quantified,
                    format!(
                        "Failed to assert size axiom for '{}::{}'",
                        datatype_name, variant.name
                    ),
                )?;
            }
        }

        // Non-negativity axiom: forall x. {dt_size(x)} dt_size(x) >= 0
        let x = self.solver.fresh_var(
            &format!("__{}_wf_x", encoding.symbol_prefix),
            carrier_sort.clone(),
        );
        let size_x = self.solver.try_apply(&size_func, &[x]).map_err(|err| {
            datatype_error(format!(
                "Failed to apply size function for non-negativity of '{}': {}",
                datatype_name, err
            ))
        })?;
        let nonneg = self.solver.try_ge(size_x, zero).map_err(|err| {
            datatype_error(format!(
                "Failed to build non-negativity guard for '{}': {}",
                datatype_name, err
            ))
        })?;
        let trigger_groups = [vec![size_x]];
        let trigger_refs: Vec<&[Term]> = trigger_groups.iter().map(Vec::as_slice).collect();
        let quantified = self
            .solver
            .try_forall_with_triggers(&[x], nonneg, &trigger_refs)
            .map_err(|err| {
                datatype_error(format!(
                    "Failed to quantify non-negativity axiom for '{}': {}",
                    datatype_name, err
                ))
            })?;
        self.assert_axiom(
            quantified,
            format!(
                "Failed to assert non-negativity axiom for '{}'",
                datatype_name
            ),
        )?;

        // Store the size function for use in decreases encoding and tests
        self.registries
            .dt_size_funcs
            .insert(datatype_name.to_string(), size_func.clone());
        self.fn_ctx
            .functions
            .insert(format!("__trust_vc_dt_size::{datatype_name}"), size_func);

        Ok(())
    }

    /// Returns the well-foundedness size UF for a recursive datatype, if registered.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn dt_size_func(&self, datatype_name: &str) -> Option<&FuncDecl> {
        self.registries.dt_size_funcs.get(datatype_name)
    }

    /// Returns whether an invariant UF has been registered for the type.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn has_type_invariant(&self, type_name: &str) -> bool {
        self.registries.type_invariant_funcs.contains_key(type_name)
    }

    /// Emit a type invariant UF and its defining axiom. Part of #2419 Slice 2.
    ///
    /// Declares `inv_TypeName: Int -> Bool` and asserts:
    /// `forall v. {inv_TypeName(v)} inv_TypeName(v) <==> body(sel_f1(v), ...)`
    ///
    /// The invariant body TrustVcExpr uses `Var { name: "field_name" }` nodes
    /// which are bound to selector applications on the universally quantified `v`.
    pub(crate) fn emit_type_invariant(
        &mut self,
        type_name: &str,
        body: &crate::ir::TrustVcExpr,
    ) -> TrustVcResult<()> {
        let encoding = self
            .registries
            .datatypes
            .get(type_name)
            .cloned()
            .ok_or_else(|| {
                datatype_error(format!(
                    "Type '{}' must be registered as a datatype before emitting invariant",
                    type_name
                ))
            })?;

        // For single-variant structs, use the first (only) variant's selectors
        // and the field metadata cached in the registered variant encoding.
        let variant_enc = encoding.variants.first().ok_or_else(|| {
            datatype_error(format!(
                "Datatype '{}' has no variants for invariant encoding",
                type_name
            ))
        })?;

        let fields = variant_enc.fields.clone();

        if fields.len() != variant_enc.selectors.len() {
            return Err(datatype_error(format!(
                "Field count mismatch for '{}': {} fields but {} selectors",
                type_name,
                fields.len(),
                variant_enc.selectors.len()
            )));
        }

        // Declare invariant UF: inv_TypeName : {Datatype} -> Bool over the native
        // carrier sort (was Int -> Bool; the invariant ranges over datatype values
        // and applies the variant's selectors, which take the carrier sort).
        let carrier_sort = super::datatype_carrier_sort(type_name);
        let inv_name = format!("inv_{}", sanitize_symbol(type_name));
        let inv_func = self
            .solver
            .try_declare_fun(&inv_name, std::slice::from_ref(&carrier_sort), Sort::Bool)
            .map_err(|err| {
                datatype_error(format!(
                    "Failed to declare invariant UF '{}': {}",
                    inv_name, err
                ))
            })?;

        // Create bound variable for the defining axiom
        let v = self.solver.fresh_var(
            &format!("__inv_{}_v", sanitize_symbol(type_name)),
            carrier_sort.clone(),
        );

        // Build variable map: field names → selector applications on v
        let mut field_vars = std::collections::HashMap::new();
        let mut field_var_types = std::collections::HashMap::new();
        for (selector, (field_name, field_ty)) in variant_enc.selectors.iter().zip(fields.iter()) {
            let sel_v = self.solver.try_apply(selector, &[v]).map_err(|err| {
                datatype_error(format!(
                    "Failed to apply selector for field '{}' in invariant of '{}': {}",
                    field_name, type_name, err
                ))
            })?;
            field_vars.insert(field_name.clone(), sel_v);
            field_var_types.insert(field_name.clone(), field_ty.clone());
        }

        // Encode the invariant body using selector terms as field bindings.
        // Scoped so the parser (which borrows self.solver) is dropped before
        // we continue using self.solver for the axiom.
        //
        // BINDER-CAPTURE backstop (see `encoder::binder_capture`): the body is
        // encoded BEFORE the `forall v` below is built, i.e. this is an
        // encode-then-close site. Watermark the assertion stack first so a
        // helper hoist that mentions `v` cannot be silently captured by the
        // closing binder.
        let capture_watermark = self.assertion_watermark();
        let body_term = {
            let mut col_lengths = std::collections::HashMap::new();
            let funcs = std::collections::HashMap::new();
            let mut parser = crate::encoder::parser_state::AstExpressionParser::new(
                &mut self.solver,
                &field_vars,
                &mut col_lengths,
                &field_var_types,
                &funcs,
            );
            // The body is destined for the body of `forall v`: let the
            // capture-aware helpers (`match_encode.rs`, `arith/int_arith.rs`)
            // INLINE their result rather than hoist a fresh const, exactly as
            // `trait_encoding_axioms` propagates the flag before its own
            // encode-then-close.
            parser.pending_universal_closure = true;
            let body_term = parser.encode_trust_vc_expr(body).map_err(|err| {
                datatype_error(format!(
                    "Failed to encode invariant body for '{}': {}",
                    type_name, err
                ))
            });
            self.state.diagnostics.merge(&parser.diagnostics);
            body_term?
        };

        // Build: inv_T(v) <==> body
        let inv_v = self.solver.try_apply(&inv_func, &[v]).map_err(|err| {
            datatype_error(format!(
                "Failed to apply invariant UF for '{}': {}",
                type_name, err
            ))
        })?;
        let iff = self.solver.try_eq(inv_v, body_term).map_err(|err| {
            datatype_error(format!(
                "Failed to build invariant iff for '{}': {}",
                type_name, err
            ))
        })?;

        // Quantify: forall v. {inv_T(v)} inv_T(v) <==> body — unless a hoist
        // made during the body encode mentions `v`, in which case building the
        // `forall` would capture it and the defining axiom is DECLINED instead
        // (see `encoder::binder_capture`). On decline `inv_T` stays
        // uninterpreted: assuming `inv_T(param)` then constrains nothing
        // (weaker context) and any obligation on `inv_T` becomes unprovable —
        // fail-closed in both directions.
        match self.binder_capture_since(capture_watermark, &[v]) {
            Some(capture) => {
                self.record_binder_capture(&format!("datatype_invariant:{type_name}"), &capture);
            }
            None => {
                let trigger_groups = [vec![inv_v]];
                let trigger_refs: Vec<&[Term]> =
                    trigger_groups.iter().map(Vec::as_slice).collect();
                let quantified = self
                    .solver
                    .try_forall_with_triggers(&[v], iff, &trigger_refs)
                    .map_err(|err| {
                        datatype_error(format!(
                            "Failed to quantify invariant axiom for '{}': {}",
                            type_name, err
                        ))
                    })?;
                self.assert_axiom(
                    quantified,
                    format!("Failed to assert invariant axiom for '{}'", type_name),
                )?;
            }
        }

        // Store the invariant UF for use in parameter assumptions
        self.registries
            .type_invariant_funcs
            .insert(type_name.to_string(), inv_func);

        Ok(())
    }

    /// Assert `inv_TypeName(term)` for a parameter of an invariant-bearing type.
    /// Part of #2419 Slice 2.
    pub(crate) fn assert_type_invariant_on_term(
        &mut self,
        type_name: &str,
        term: Term,
    ) -> TrustVcResult<()> {
        let inv_func = self
            .registries
            .type_invariant_funcs
            .get(type_name)
            .cloned()
            .ok_or_else(|| {
                datatype_error(format!(
                    "No invariant UF registered for type '{}'",
                    type_name
                ))
            })?;
        let inv_term = self.solver.try_apply(&inv_func, &[term]).map_err(|err| {
            datatype_error(format!(
                "Failed to apply invariant for '{}': {}",
                type_name, err
            ))
        })?;
        self.assert_axiom(
            inv_term,
            format!(
                "Failed to assert type invariant assumption for '{}'",
                type_name
            ),
        )
    }
}
