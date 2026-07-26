//! Function-call encoding for TrustVcExpr IR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Term;

use crate::encoder::types::sort_for_type;
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{TrustVcExpr, TrustVcType};
#[cfg(feature = "native-strings")]
use crate::ir_expr::{NATIVE_STRING_ENDS_WITH_FN, NATIVE_STRING_STARTS_WITH_FN};
use crate::ir_lowering::infer_expr_type;

// ay 6c423022 still needs this bridge for Poly -> concrete result
// roundtrips. Removing it makes the focused polymorphism suite return SAT for
// identity/first call obligations that should verify; keep the gate explicit so
// the workaround can be re-probed when ay's cross-sort congruence improves.
const ASSERT_POLY_RESULT_CONGRUENCE_HINT: bool = true;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InternalClosureUf {
    Apply,
    Requires,
    Ensures,
}

/// Recognizes the exact IR shapes emitted by the three first-class closure UF
/// builders. Prefix checks alone are not provenance: a source-level function
/// with a colliding name could otherwise lend its body axiom to an opaque call
/// or borrow the apply result's codomain axiom and verify by contradiction.
fn classify_internal_closure_uf(
    name: &str,
    args: &[TrustVcExpr],
    return_ty: &TrustVcType,
) -> Option<InternalClosureUf> {
    let Some((function, application_args)) = args.split_first() else {
        return None;
    };
    let TrustVcType::SpecFn(param_tys, declared_return_ty) = infer_expr_type(function) else {
        return None;
    };
    let arguments_match = |arguments: &[TrustVcExpr]| {
        arguments.len() == param_tys.len()
            && arguments
                .iter()
                .zip(&param_tys)
                .all(|(argument, expected)| infer_expr_type(argument) == *expected)
    };
    if arguments_match(application_args)
        && declared_return_ty.as_ref() == return_ty
        && name == crate::ir_builder::spec_fn_apply_symbol(&param_tys, return_ty)
    {
        return Some(InternalClosureUf::Apply);
    }
    if return_ty == &TrustVcType::Bool
        && arguments_match(application_args)
        && name == crate::ir_builder::call_requires_symbol(&param_tys)
    {
        return Some(InternalClosureUf::Requires);
    }
    if return_ty == &TrustVcType::Bool
        && application_args.len() == param_tys.len() + 1
        && arguments_match(&application_args[..param_tys.len()])
        && application_args
            .last()
            .is_some_and(|result| infer_expr_type(result) == *declared_return_ty)
        && name == crate::ir_builder::call_ensures_symbol(&param_tys, declared_return_ty.as_ref())
    {
        return Some(InternalClosureUf::Ensures);
    }
    None
}

impl<'a> AstExpressionParser<'a> {
    /// Encode a named function call.
    ///
    /// For polymorphic functions (those with TypeParam parameters), infers
    /// concrete type bindings from argument types and wraps/unwraps values
    /// through Box_T/Unbox_T to bridge between concrete sorts and the
    /// type-erased Poly sort. Part of #2053.
    ///
    /// Tracks width/signedness metadata from `return_ty` when BV-typed, so
    /// downstream consumers (checked/saturating arithmetic) can derive correct
    /// overflow semantics without falling back to defaults. Fixes #2100.
    /// Asserts that an opaque Int-sorted `term` inhabits `ty`'s integer codomain:
    /// bounded types get `lo <= term < hi`, `nat` gets `term >= 0`, `char` gets
    /// the Unicode scalar-value domain. A no-op for unbounded `int` and for
    /// non-integer types. Mirrors [`add_integer_range_guards`] but ASSERTS the
    /// range on a ground term instead of guarding a quantifier body.
    ///
    /// Only sound when `term` is OPAQUE (no body axiom that could pin it outside
    /// its declared type — which would make the range a contradiction and vacuously
    /// verify). Used for spec_fn apply UFs, which carry no body.
    fn assert_int_codomain_range(&mut self, term: Term, ty: &TrustVcType) -> TrustVcResult<()> {
        use crate::encoder::quantifiers::{integer_range_bounds, lower_bound_only};
        if matches!(ty, TrustVcType::Char) {
            let guard = self.char_domain_guard(term)?;
            self.solver
                .try_assert_term(guard)
                .map_err(|e| e.to_string())?;
            return Ok(());
        }
        if let Some((lower_val, upper_val)) = integer_range_bounds(ty) {
            let lower_term = self.solver.int_const_bigint(&lower_val);
            let lower = self
                .solver
                .try_ge(term, lower_term)
                .map_err(|e| e.to_string())?;
            let upper_term = self.solver.int_const_bigint(&upper_val);
            let upper = self
                .solver
                .try_lt(term, upper_term)
                .map_err(|e| e.to_string())?;
            let range = self
                .solver
                .try_and(lower, upper)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(range)
                .map_err(|e| e.to_string())?;
        } else if let Some(lower_val) = lower_bound_only(ty) {
            let lower_term = self.solver.int_const_bigint(&lower_val);
            let guard = self
                .solver
                .try_ge(term, lower_term)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(guard)
                .map_err(|e| e.to_string())?;
        }
        Ok(())
    }

    pub(super) fn encode_fn_call(
        &mut self,
        name: &str,
        args: &[TrustVcExpr],
        return_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        #[cfg(feature = "native-strings")]
        if matches!(
            name,
            NATIVE_STRING_STARTS_WITH_FN | NATIVE_STRING_ENDS_WITH_FN
        ) {
            return self.encode_native_string_fn_call(name, args);
        }

        if name == "__trust_vc_dt_size" {
            return self.encode_dt_size_builtin(args);
        }

        if name == crate::extensional_eq::STRICT_EQ_FN {
            return self.encode_strict_eq_builtin(args);
        }

        if name == crate::ir_lowering::SEQ_FROM_FN_BUILTIN {
            #[cfg(feature = "native-seq")]
            {
                return self.native_seq_from_fn(args, return_ty);
            }
            #[cfg(not(feature = "native-seq"))]
            {
                return self.encode_seq_from_fn(args, return_ty);
            }
        }

        if name == crate::ir_lowering::SET_NEW_BUILTIN {
            // Memoize closed comprehensions so every occurrence of the same
            // `Set::new(|x| pred)` in one query shares one backend set + axiom,
            // letting downstream image/membership facts connect (GAP3). #2778.
            let skip_memo = self.refs_transient_local_binding(&args.iter().collect::<Vec<_>>());
            let key = format!("set_new::{:?}::{:?}", return_ty, args);
            return self
                .memoized_pure_collection(skip_memo, key, |s| s.encode_set_new(args, return_ty));
        }

        if args.is_empty() && !self.functions.contains_key(name) {
            let result = self.encode_var(name, return_ty)?;

            if self.quantifier_depth == 0 {
                if let Some(pool) = self.ground_pool.as_deref_mut() {
                    pool.register_expr(name, Vec::new(), Vec::new());
                }
            }

            return Ok(result);
        }

        let internal_closure_uf = classify_internal_closure_uf(name, args, return_ty);
        if internal_closure_uf.is_some() && self.functions.contains_key(name) {
            return Err(format!(
                "source function '{name}' collides with a reserved internal closure UF"
            )
            .into());
        }
        let opaque_spec_fn_apply = internal_closure_uf == Some(InternalClosureUf::Apply);

        // Clone a source FuncDecl to avoid a borrow conflict with &mut self.
        // Internal SpecFn application UFs are generated during expression
        // rewriting, so they do not come from a source-level function context.
        let func_decl = if let Some(decl) = self.functions.get(name).cloned() {
            decl
        } else if internal_closure_uf.is_some() {
            // Internal per-signature UF symbols synthesized during expression
            // rewriting: `spec_fn_apply` (opaque application) and the Phase C
            // closure reflection predicates `call_requires%` / `call_ensures%`.
            // Each carries its return sort in the FnCall (`Bool` for the two
            // reflection predicates), so `sort_for_type(return_ty)` yields a
            // Bool-sorted predicate for them automatically. Declare the UF via
            // AY's native API instead of forging a `FuncDecl` handle: AY now
            // rejects undeclared handles at `try_apply`, and repeated identical
            // declarations are intentionally idempotent.
            let domain: Vec<_> = args
                .iter()
                .map(|arg| sort_for_type(&infer_expr_type(arg)))
                .collect();
            self.solver
                .try_declare_fun(name, &domain, sort_for_type(return_ty))
                .map_err(|e| e.to_string())?
        } else {
            return Err(format!("Undefined function: {name}").into());
        };

        // Infer type bindings for polymorphic calls (#2053).
        let type_bindings = infer_type_bindings(
            name,
            args,
            self.function_param_types,
            self.function_type_params,
        );
        let param_types: Option<Vec<TrustVcType>> =
            self.function_param_types.and_then(|m| m.get(name).cloned());

        let mut arg_terms = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            let mut term = self.encode_subexpr(arg)?;

            // Box concrete args into Poly when param expects TypeParam (#2053).
            if let Some(ref pts) = param_types {
                if let Some(TrustVcType::TypeParam(tp_name)) = pts.get(i) {
                    if let Some(concrete_ty) = type_bindings.get(tp_name) {
                        if let Some(ref mut poly_ctx) = self.poly_context {
                            let (box_fn, unbox_fn) =
                                poly_ctx.ensure_box_unbox(self.solver, concrete_ty)?;
                            let concrete_term = term;
                            term = self
                                .solver
                                .try_apply(&box_fn, &[concrete_term])
                                .map_err(|e| e.to_string())?;
                            // Ground roundtrip instance: Unbox_T(Box_T(y)) == y.
                            // PolyContext declares Box/Unbox as UFs and does not
                            // assert a universal roundtrip axiom, so concrete
                            // polymorphic calls need this ground semantic bridge.
                            let unboxed = self
                                .solver
                                .try_apply(&unbox_fn, &[term])
                                .map_err(|e| e.to_string())?;
                            let roundtrip_eq = self
                                .solver
                                .try_eq(unboxed, concrete_term)
                                .map_err(|e| e.to_string())?;
                            self.solver
                                .try_assert_term(roundtrip_eq)
                                .map_err(|e| e.to_string())?;
                        }
                    }
                }
            }

            arg_terms.push(term);
        }

        let mut result = self
            .solver
            .try_apply(&func_decl, &arg_terms)
            .map_err(|e| e.to_string())?;

        if matches!(return_ty, TrustVcType::Unit) {
            super::super::unit::assert_unit_term(
                self.solver,
                result,
                "encode function call",
                name,
            )?;
        }

        // spec_fn return-type refinement: an opaque `spec_fn(..) -> T` apply UF
        // is otherwise unconstrained, but its result inhabits `T`'s codomain by
        // the closure's type. In int mode, assert that range on the result — a
        // `-> nat` apply is `>= 0`, `-> u8` is `0..256`, etc. Sound because the
        // apply UF carries NO body axiom (see the `spec_fn_apply` opaqueness
        // note in ir_lowering::dispatch::calls), so nothing can pin the result
        // outside its declared type; the refinement can never contradict. In BV
        // mode a bounded-width result is already range-carried by its sort.
        if self.int_mode() && opaque_spec_fn_apply {
            self.assert_int_codomain_range(result, return_ty)?;
        }

        // Unbox the type-erased Poly result back to a concrete sort when the
        // DECLARED return type is a `TypeParam` (#2053, #2778).
        //
        // The lowering may have monomorphized a generic fn's `TypeParam` return
        // into a concrete carrier (so a following field projection like
        // `projected.a` resolves); the backend `FuncDecl` is still built from the
        // DECLARED signature, so `result` is Poly-sorted and must be bridged back
        // through `Unbox_T`. Two shapes reach here:
        //   * `return_ty` is the unsubstituted `TypeParam` — the concrete target
        //     comes from the argument-inferred `type_bindings`;
        //   * `return_ty` is a lowering-monomorphized concrete carrier — recover
        //     the declared `TypeParam` name from `function_return_types`; the
        //     concrete target IS this `return_ty`.
        let bridge_target: Option<(String, TrustVcType)> = match return_ty {
            TrustVcType::TypeParam(tp_name) => type_bindings
                .get(tp_name)
                .map(|concrete| (tp_name.clone(), concrete.clone())),
            concrete => self
                .function_return_types
                .and_then(|m| m.get(name))
                .and_then(|declared| match declared {
                    TrustVcType::TypeParam(tp_name) => Some((tp_name.clone(), concrete.clone())),
                    _ => None,
                }),
        };
        if let Some((tp_name, concrete_ty)) = bridge_target {
            let tp_name = tp_name.as_str();
            let concrete_ty = &concrete_ty;
            {
                let fn_result_poly = result; // Poly-sorted before unboxing
                if let Some(ref mut poly_ctx) = self.poly_context {
                    let (_box_fn, unbox_fn) =
                        poly_ctx.ensure_box_unbox(self.solver, concrete_ty)?;
                    result = self
                        .solver
                        .try_apply(&unbox_fn, &[fn_result_poly])
                        .map_err(|e| e.to_string())?;
                    if matches!(concrete_ty, TrustVcType::Unit) {
                        super::super::unit::assert_unit_term(
                            self.solver,
                            result,
                            "encode function call",
                            name,
                        )?;
                    }

                    // ay 6c423022 evidence: without this implication, the
                    // pure solver and end-to-end polymorphic identity tests
                    // return SAT for `Unbox_T(f(Box_T(y))) == y`. The hint is
                    // a tautological congruence instance linking the Poly
                    // body-axiom equality to the concrete Unbox projection.
                    if ASSERT_POLY_RESULT_CONGRUENCE_HINT {
                        if let Some(ref pts) = param_types {
                            for (i, pt) in pts.iter().enumerate() {
                                if let TrustVcType::TypeParam(param_tp) = pt {
                                    if param_tp.as_str() == tp_name {
                                        if let Some(boxed) = arg_terms.get(i).copied() {
                                            let unbox_boxed = self
                                                .solver
                                                .try_apply(&unbox_fn, &[boxed])
                                                .map_err(|e| e.to_string())?;
                                            let premise = self
                                                .solver
                                                .try_eq(fn_result_poly, boxed)
                                                .map_err(|e| e.to_string())?;
                                            let conclusion = self
                                                .solver
                                                .try_eq(result, unbox_boxed)
                                                .map_err(|e| e.to_string())?;
                                            let hint = self
                                                .solver
                                                .try_implies(premise, conclusion)
                                                .map_err(|e| e.to_string())?;
                                            self.solver
                                                .try_assert_term(hint)
                                                .map_err(|e| e.to_string())?;
                                        }
                                        break; // first matching param is enough
                                    }
                                }
                            }
                        }
                    }
                }
                // Track BV width from the concrete type, not the TypeParam.
                if !self.int_mode() {
                    if let Some(width) = concrete_ty.bit_width() {
                        let signed = !concrete_ty.is_unsigned();
                        self.term_widths.insert(result, (width, signed));
                    }
                }
            }
        }

        // Track BV width/signedness so checked/saturating arithmetic on
        // FnCall results gets correct overflow semantics (#2100).
        if !matches!(return_ty, TrustVcType::TypeParam(_)) && !self.int_mode() {
            if let Some(width) = return_ty.bit_width() {
                let signed = !return_ty.is_unsigned();
                self.term_widths.insert(result, (width, signed));
            }
        }

        if self.quantifier_depth == 0 {
            if let Some(pool) = self.ground_pool.as_deref_mut() {
                pool.register_expr(name, arg_terms.clone(), args.to_vec());
            }
        }

        Ok(result)
    }

    #[allow(clippy::indexing_slicing)] // args[0]/args[1] guarded by args.len() check
    fn encode_strict_eq_builtin(&mut self, args: &[TrustVcExpr]) -> TrustVcResult<Term> {
        if args.len() != 2 {
            return Err(format!(
                "{} expects exactly 2 arguments, got {}",
                crate::extensional_eq::STRICT_EQ_FN,
                args.len()
            )
            .into());
        }

        let left_hint_ty = self.infer_effective_expr_type(&args[1], None);
        let right_hint_ty = self.infer_effective_expr_type(&args[0], None);
        let left = self.encode_expr_with_integer_hint(&args[0], Some(&left_hint_ty))?;
        let right = self.encode_expr_with_integer_hint(&args[1], Some(&right_hint_ty))?;
        let (left, right) = self.coerce_bv_widths(left, right)?;
        let raw_eq = self
            .solver
            .try_eq(left, right)
            .map_err(|err| err.to_string())?;

        // Extensionality bridge (sound, additive). For the mathematical value
        // types Verus identifies by their extension (Set/Map/Seq/Multiset/SpecFn),
        // extensional equality IS equality: `ext_eq(a,b) => a == b` is a theorem
        // (set/map/seq/multiset extensionality; function extensionality for
        // SpecFn). We assert ONLY that implication as a background axiom — never
        // its premise. So `===` stays strict: the raw-eq goal still requires the
        // extensional formula to be independently entailed (e.g. a prior, VERIFIED
        // `=~=` carried forward as an assumption, or a genuine source hypothesis).
        // Without an established extensional equality the premise is not entailed
        // and `===` is unaffected, so no false `==` can be manufactured. The
        // premise `build_ext_eq_expr(a,b)` is built deterministically from the
        // same operands, so it hash-conses to the SAME term as a forwarded `=~=`
        // assumption over those operands, making modus ponens fire at the boolean
        // level. Gated to the extensional types; raw `===` over scalars/structs is
        // untouched. Part of the auto-`ext_equal` parity work.
        if Self::strict_eq_extensionality_bridge_applies(&args[0], &args[1]) {
            let ext_formula =
                crate::extensional_eq::build_ext_eq_expr(args[0].clone(), args[1].clone());
            let ext_term = self.encode_subexpr(&ext_formula)?;
            let implication = self
                .solver
                .try_implies(ext_term, raw_eq)
                .map_err(|err| err.to_string())?;
            self.solver
                .try_assert_term(implication)
                .map_err(|err| err.to_string())?;
        }

        Ok(raw_eq)
    }

    /// True iff the extensionality bridge `ext_eq(a,b) => a == b` is sound and
    /// non-trivial for these `===` operands.
    ///
    /// Restricted to equal-typed operands of the mathematical value types Verus
    /// treats extensionally (Set/Map/Seq/Multiset/SpecFn, plus String/StrSlice
    /// whose extension is the underlying char Seq). For every other type
    /// `build_ext_eq_expr` collapses to raw equality and the bridge would be a
    /// vacuous `eq => eq`, so it is skipped to leave scalar/struct `===` and the
    /// common-case solver state untouched.
    fn strict_eq_extensionality_bridge_applies(lhs: &TrustVcExpr, rhs: &TrustVcExpr) -> bool {
        let lhs_ty = infer_expr_type(lhs);
        if lhs_ty != infer_expr_type(rhs) {
            return false;
        }
        matches!(
            lhs_ty,
            TrustVcType::Seq(_)
                | TrustVcType::Set(_)
                | TrustVcType::Multiset(_)
                | TrustVcType::Map(_, _)
                | TrustVcType::SpecFn(_, _)
                | TrustVcType::String
                | TrustVcType::StrSlice
        )
    }

    #[allow(clippy::indexing_slicing)] // args[0] guarded by args.len() != 1
    fn encode_dt_size_builtin(&mut self, args: &[TrustVcExpr]) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!(
                "__trust_vc_dt_size expects exactly 1 argument, got {}",
                args.len()
            )
            .into());
        }

        let datatype_name = match infer_expr_type(&args[0]) {
            TrustVcType::Datatype { name, .. } | TrustVcType::RecursiveRef(name) => name,
            other => {
                return Err(format!(
                    "__trust_vc_dt_size requires a recursive datatype argument, got '{}'",
                    other.to_type_string()
                )
                .into())
            }
        };

        let size_func = self
            .dt_size_funcs
            .as_ref()
            .and_then(|funcs| funcs.get(&datatype_name))
            .cloned()
            .or_else(|| {
                self.functions
                    .get(&format!("__trust_vc_dt_size::{datatype_name}"))
                    .cloned()
            })
            .ok_or_else(|| {
                format!(
                    "__trust_vc_dt_size has no registered size function for '{}'",
                    datatype_name
                )
            })?;

        let arg_term = self.encode_subexpr(&args[0])?;
        self.solver
            .try_apply(&size_func, &[arg_term])
            .map_err(|err| {
                format!(
                    "Failed to apply __trust_vc_dt_size for '{}': {}",
                    datatype_name, err
                )
                .into()
            })
    }

    #[cfg(feature = "native-strings")]
    fn encode_native_string_fn_call(
        &mut self,
        name: &str,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 2 {
            return Err(format!("{name} expects exactly 2 arguments, got {}", args.len()).into());
        }

        let haystack = self.encode_subexpr(&args[0])?;
        let needle = self.encode_subexpr(&args[1])?;
        match name {
            NATIVE_STRING_STARTS_WITH_FN => self
                .solver
                .try_str_prefixof(needle, haystack)
                .map_err(|e| e.to_string().into()),
            NATIVE_STRING_ENDS_WITH_FN => self
                .solver
                .try_str_suffixof(needle, haystack)
                .map_err(|e| e.to_string().into()),
            _ => unreachable!("guarded by caller"),
        }
    }
}

/// Infer type parameter -> concrete type bindings from argument types.
///
/// For each parameter typed as `TypeParam("T")`, look at the corresponding
/// argument's inferred type to determine what concrete type `T` binds to.
/// Returns an empty map for monomorphic functions. Part of #2053.
fn infer_type_bindings(
    fn_name: &str,
    args: &[TrustVcExpr],
    fn_param_types: Option<&std::collections::HashMap<String, Vec<TrustVcType>>>,
    fn_type_params: Option<&std::collections::HashMap<String, Vec<String>>>,
) -> std::collections::HashMap<String, TrustVcType> {
    let mut bindings = std::collections::HashMap::new();

    let type_params = match fn_type_params.and_then(|m| m.get(fn_name)) {
        Some(tps) if !tps.is_empty() => tps,
        _ => return bindings, // monomorphic - no bindings needed
    };

    let param_types = match fn_param_types.and_then(|m| m.get(fn_name)) {
        Some(pts) => pts,
        None => return bindings,
    };

    for (i, param_ty) in param_types.iter().enumerate() {
        if let TrustVcType::TypeParam(tp_name) = param_ty {
            if type_params.contains(tp_name) {
                if let Some(arg) = args.get(i) {
                    let concrete_ty = infer_expr_type(arg);
                    // Only bind if the arg type is concrete (not another TypeParam)
                    if !matches!(concrete_ty, TrustVcType::TypeParam(_) | TrustVcType::Poly) {
                        bindings.entry(tp_name.clone()).or_insert(concrete_ty);
                    }
                }
            }
        }
    }

    bindings
}

#[cfg(test)]
mod internal_closure_uf_tests {
    use super::{classify_internal_closure_uf, InternalClosureUf};
    use crate::ir::{TrustVcExpr, TrustVcType};

    fn receiver() -> TrustVcExpr {
        crate::ir_builder::var(
            "f",
            TrustVcType::SpecFn(vec![TrustVcType::MathInt], Box::new(TrustVcType::Nat)),
        )
    }

    fn int_argument() -> TrustVcExpr {
        crate::ir_builder::int_lit(0, TrustVcType::MathInt)
    }

    #[test]
    fn internal_closure_uf_requires_exact_application_argument_types() {
        let apply =
            crate::ir_builder::spec_fn_apply_symbol(&[TrustVcType::MathInt], &TrustVcType::Nat);
        assert_eq!(
            classify_internal_closure_uf(&apply, &[receiver(), int_argument()], &TrustVcType::Nat,),
            Some(InternalClosureUf::Apply),
        );
        assert_eq!(
            classify_internal_closure_uf(
                &apply,
                &[receiver(), TrustVcExpr::BoolLit(false)],
                &TrustVcType::Nat,
            ),
            None,
        );

        let requires = crate::ir_builder::call_requires_symbol(&[TrustVcType::MathInt]);
        assert_eq!(
            classify_internal_closure_uf(
                &requires,
                &[receiver(), TrustVcExpr::BoolLit(false)],
                &TrustVcType::Bool,
            ),
            None,
        );
    }

    #[test]
    fn internal_closure_uf_requires_exact_ensures_result_type() {
        let ensures =
            crate::ir_builder::call_ensures_symbol(&[TrustVcType::MathInt], &TrustVcType::Nat);
        assert_eq!(
            classify_internal_closure_uf(
                &ensures,
                &[receiver(), int_argument(), TrustVcExpr::BoolLit(false)],
                &TrustVcType::Bool,
            ),
            None,
        );
        assert_eq!(
            classify_internal_closure_uf(
                &ensures,
                &[
                    receiver(),
                    int_argument(),
                    crate::ir_builder::int_lit(0, TrustVcType::Nat),
                ],
                &TrustVcType::Bool,
            ),
            Some(InternalClosureUf::Ensures),
        );
    }
}
