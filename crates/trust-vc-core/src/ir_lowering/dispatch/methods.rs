//! Method, field, and struct-literal lowering helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2526.

use std::collections::BTreeSet;

use super::super::{
    infer_expr_type, lower_syn_expr_with_depth, operators::coerce_unsuffixed_literal,
    path_to_string, LoweringError, TypeEnv,
};
use super::collections::{
    coerce_collection_literal_args, coerce_literal_to_receiver_type, collection_op_supported,
    collection_surface, extract_receiver_name, infer_collection_op_type,
    invalid_collection_receiver_error, lowered_receiver_name, match_collection_op,
    unsupported_collection_op_error, CollectionSurface,
};
use super::option_closure::{parse_option_closure_arg, OptionClosureArg};
use super::spec_closure::lower_spec_fn_arg;
use crate::encoder::datatype::{selector_symbol_name, tester_symbol_name, variant_symbol_name};
use crate::ir::{DatatypeVariant, TrustVcType};
use crate::ir_expr::{
    ArithOp, CollectionOp, CompareOp, LogicOp, MatchArm, MatchPattern, SpecialArithOp, TrustVcExpr,
    WrappingMode,
};
use crate::ir_lowering::env::{
    DatatypeVariantMeta, OptionBindingMeta, OptionBindingState, ResultBindingMeta,
    ResultBindingState,
};

pub(in crate::ir_lowering) fn lower_method_call(
    mc: &syn::ExprMethodCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let method = mc.method.to_string();
    let receiver_name = extract_receiver_name(&mc.receiver);

    if let Some(prophecy_expr) =
        lower_prophecy_method_call(&method, receiver_name.as_deref(), &mc.args, env, depth)?
    {
        return Ok(prophecy_expr);
    }

    let receiver = lower_syn_expr_with_depth(&mc.receiver, env, depth)?;
    let receiver_name = receiver_name.or_else(|| lowered_receiver_name(&receiver));
    let receiver_ty = infer_expr_type(&receiver);

    // `.iter()` on a Seq (a `&[T]`/`Vec<T>` view) is a no-op in the ghost model:
    // the `Seq` IS the iterable. Returning the receiver unchanged lets a chained
    // adapter such as `constraints.iter().all(..)` see the `Seq` directly, so the
    // `.all`/`.any` quantifier lowering below fires with a `Seq` receiver.
    if method == "iter" && mc.args.is_empty() && matches!(receiver_ty, TrustVcType::Seq(_)) {
        return Ok(receiver);
    }
    // `seq.all(|x| p(x))` / `seq.any(|x| p(x))` over a `Seq` lower to a bounded
    // universal/existential quantifier over the index range — the spec semantics
    // of the `Iterator::all`/`any` fold (`forall i. i < len ==> p(seq[i])`).
    if let Some(expr) = lower_seq_quantifier_method(&method, mc, &receiver_ty, env, depth)? {
        return Ok(expr);
    }

    if let Some(expr) = lower_partial_ord_integer_method_call(
        &method,
        mc,
        env,
        depth,
        receiver.clone(),
        &receiver_ty,
    )? {
        return Ok(expr);
    }

    if let Some(expr) =
        lower_partial_eq_method_call(&method, mc, env, depth, receiver.clone(), &receiver_ty)?
    {
        return Ok(expr);
    }

    if let Some(expr) = lower_minmax_abs_integer_method_call(
        &method,
        mc,
        env,
        depth,
        receiver.clone(),
        &receiver_ty,
    )? {
        return Ok(expr);
    }

    if method == "call" {
        if let TrustVcType::SpecFn(arg_tys, ret_ty) = &receiver_ty {
            if arg_tys.len() != 1 {
                return Err(LoweringError::UnsupportedMethod(format!(
                    "SpecFn::call currently supports unary SpecFn values, got {} arguments",
                    arg_tys.len()
                )));
            }
            if mc.args.len() != 1 {
                return Err(LoweringError::UnsupportedMethod(format!(
                    "SpecFn::call expects 1 arg, got {}",
                    mc.args.len()
                )));
            }
            let arg = single_method_arg(&method, &mc.args)?;
            let lowered = lower_syn_expr_with_depth(arg, env, depth)?;
            let lowered = coerce_unsuffixed_literal(lowered, &arg_tys[0]);
            return Ok(crate::ir_builder::spec_fn_apply(
                receiver,
                arg_tys,
                vec![lowered],
                ret_ty.as_ref().clone(),
            ));
        }
    }

    // Phase C closure reflection: `f.requires((a, ..))` / `f.ensures((a, ..), r)`
    // on a first-class `SpecFn` value lower to the OPAQUE Bool UF predicates
    // `call_requires%` / `call_ensures%`. Their meaning is fixed solely by the
    // definitional axiom co-emitted at the closure literal; direct application
    // `f(..)` stays deferred (fail closed). Reflection is usable in
    // assert!/contract position only.
    if method == "requires" || method == "ensures" {
        if let TrustVcType::SpecFn(arg_tys, ret_ty) = &receiver_ty {
            return lower_spec_fn_reflection(&method, mc, receiver, arg_tys, ret_ty, env, depth);
        }
    }

    if !env.source_type_shadows_builtin("Option") {
        if let Some(expr) = lower_option_method_call(
            &method,
            mc,
            env,
            depth,
            receiver.clone(),
            receiver_name.clone(),
            &receiver_ty,
        )? {
            return Ok(expr);
        }
    }

    if !env.source_type_shadows_builtin("Result") {
        if let Some(expr) = lower_result_method_call(
            &method,
            mc,
            receiver.clone(),
            receiver_name.clone(),
            &receiver_ty,
            env,
        )? {
            return Ok(expr);
        }
    }

    if let Some(expr) = lower_cow_view_method_call(
        &method,
        mc,
        receiver.clone(),
        receiver_name.clone(),
        &receiver_ty,
    )? {
        return Ok(expr);
    }

    #[cfg(feature = "native-strings")]
    if receiver_ty.is_string_like() {
        return lower_native_string_method_call(
            &method,
            mc,
            env,
            depth,
            receiver,
            receiver_name,
            &receiver_ty,
        );
    }

    if let Some(op) = match_collection_op(&method, &receiver_ty) {
        match collection_surface(&receiver_ty) {
            CollectionSurface::DirectCollection => {
                if !collection_op_supported(&receiver_ty, &op) {
                    return Err(unsupported_collection_op_error(&op, &receiver_ty));
                }
                // The combinator ops carry their spec predicate/mapping closure
                // at a fixed argument index. Normalize a bare closure there into
                // an implicit `SpecFn::new(...)`, inferring untyped binder types
                // from the receiver (fold's accumulator from the already-lowered
                // init arg). All other args keep generic lowering, and the op's
                // own typing (`infer_collection_op_type`) re-validates the
                // resulting `SpecFn` signature, so this only ever fails closed.
                let closure_idx = spec_closure_arg_index(&op);
                let mut args = Vec::with_capacity(mc.args.len());
                for (index, arg) in mc.args.iter().enumerate() {
                    if Some(index) == closure_idx {
                        let expected = spec_closure_expected_params(&op, &receiver_ty, &args);
                        args.push(lower_spec_fn_arg(arg, env, depth, expected.as_deref())?);
                    } else {
                        args.push(lower_syn_expr_with_depth(arg, env, depth)?);
                    }
                }
                let args = coerce_collection_literal_args(&op, &receiver_ty, args);
                let ty = infer_collection_op_type(&op, &receiver_ty, &args)?;
                return Ok(TrustVcExpr::CollectionOp {
                    op,
                    receiver: Box::new(receiver),
                    receiver_name,
                    args,
                    ty,
                });
            }
            CollectionSurface::ViewOnly(view_ty) => {
                if op == CollectionOp::View {
                    return Ok(TrustVcExpr::CollectionOp {
                        op,
                        receiver: Box::new(receiver),
                        receiver_name,
                        args: vec![],
                        ty: view_ty,
                    });
                }
                return Err(LoweringError::UnsupportedMethod(format!(
                    "{} on '{}' is unsupported in this slice; use {}.view()...",
                    method,
                    receiver_ty.to_type_string(),
                    receiver_name
                        .clone()
                        .unwrap_or_else(|| "the string value".to_string())
                )));
            }
            CollectionSurface::None => {}
        }
    }
    if method == "view" {
        if !mc.args.is_empty() {
            return Err(LoweringError::UnsupportedMethod(format!(
                "view expects 0 args, got {}",
                mc.args.len()
            )));
        }

        if receiver_name
            .as_deref()
            .is_some_and(|name| env.is_erased_ghost_var(name))
        {
            return Ok(receiver);
        }
    }
    if let Some((mode, op)) = match_wrapping_method(&method) {
        if mc.args.len() != 1 {
            return Err(LoweringError::UnsupportedMethod(format!(
                "{} expects 1 arg, got {}",
                method,
                mc.args.len()
            )));
        }
        let arg = single_method_arg(&method, &mc.args)?;
        let ty = receiver_ty.clone();
        let right = lower_syn_expr_with_depth(arg, env, depth)?;
        let right = coerce_literal_to_receiver_type(right, &ty);
        return Ok(TrustVcExpr::WrappingArith {
            mode,
            op,
            left: Box::new(receiver),
            right: Box::new(right),
            ty,
        });
    }
    if method == "floor" && matches!(receiver_ty, TrustVcType::Real) {
        if !mc.args.is_empty() {
            return Err(LoweringError::UnsupportedMethod(format!(
                "floor expects 0 args, got {}",
                mc.args.len()
            )));
        }
        return Ok(TrustVcExpr::Cast {
            expr: Box::new(receiver),
            from_ty: TrustVcType::Real,
            to_ty: TrustVcType::MathInt,
        });
    }
    // `x.clone()` is the value-model identity `x` for any type whose `Clone` is
    // structural — primitives (incl. floats), structural tuples, and Option/Result
    // of those. The `Clone` contract requires `x.clone() == x`, which holds
    // structurally for these; a user type MAY carry a non-structural custom `Clone`
    // (like custom `PartialEq`), so those decline (fall through, fail-closed).
    if method == "clone" && is_structural_clone_type(&receiver_ty, env) {
        if !mc.args.is_empty() {
            return Err(LoweringError::UnsupportedMethod(format!(
                "clone expects 0 args, got {}",
                mc.args.len()
            )));
        }
        return Ok(receiver);
    }
    if let Some(expr) = lower_primitive_integer_trait_method_call(
        &method,
        mc,
        env,
        depth,
        receiver.clone(),
        &receiver_ty,
    )? {
        return Ok(expr);
    }
    let type_name = receiver_ty.to_type_string();
    let mut method_meta = env.lookup_method(&type_name, &method);
    if method_meta.is_none() {
        // A generic datatype receiver's type string carries its type arguments
        // (`S1<i32, i32>`), but the auto-generated accessor methods (field
        // selectors `get_V_field`, variant testers `is_V`) are keyed on the BARE
        // datatype name (`S1`) in `register_variant_helper_methods`. Retry the
        // lookup with the generic arguments stripped so a selector/tester on a
        // generic datatype resolves — e.g. `let S1(y, z) = x;` over
        // `struct S1<A, B>(A, B)`. The non-generic path already matched exactly
        // above, so this only ever adds resolution for a generic receiver.
        let base_name = type_name.split('<').next().unwrap_or(&type_name).trim();
        if base_name != type_name.as_str() {
            method_meta = env.lookup_method(base_name, &method);
        }
    }
    if let Some(meta) = method_meta {
        // Concrete-impl trait method: lift the concrete receiver into the trait
        // UF's `Poly` self-domain via the impl's `Box_T` bridge, so the call
        // becomes `Trait__method(Box_S(s), …)`. This both sort-checks against the
        // Poly self-param and matches the per-impl linking-axiom trigger; the
        // value is then supplied by the trait's postcondition axiom. `None`
        // (the generic/accessor path) passes the receiver bare, unchanged.
        let receiver_arg = if let Some(box_fn) = &meta.box_receiver {
            TrustVcExpr::FnCall {
                name: box_fn.clone(),
                args: vec![receiver],
                return_ty: TrustVcType::Poly,
            }
        } else {
            receiver
        };
        let mut args = vec![receiver_arg];
        for (index, arg) in mc.args.iter().enumerate() {
            let lowered = lower_syn_expr_with_depth(arg, env, depth)?;
            if let Some(param_ty) = meta.param_types.get(index) {
                args.push(coerce_unsuffixed_literal(lowered, param_ty));
            } else {
                args.push(lowered);
            }
        }
        return Ok(TrustVcExpr::FnCall {
            name: meta.uf_name.clone(),
            args,
            return_ty: meta.return_type.clone(),
        });
    }
    if let Some(expr) =
        lower_minmax_integer_method_call(&method, mc, env, depth, receiver.clone(), &receiver_ty)?
    {
        return Ok(expr);
    }
    if let Some(expr) =
        lower_euclidean_integer_method_call(&method, mc, env, depth, receiver, &receiver_ty)?
    {
        return Ok(expr);
    }
    if let Some(op) = match_collection_op(&method, &receiver_ty) {
        return Err(invalid_collection_receiver_error(&op, &receiver_ty));
    }
    Err(LoweringError::UnsupportedMethod(format!(
        "{method}() on type `{type_name}` — this method is not available in specification context"
    )))
}

/// Lower `seq.all(|x| p(x))` / `seq.any(|x| p(x))` over a `Seq` to a bounded
/// quantifier over the index range, mirroring the spec semantics of the
/// `Iterator::all`/`any` fold:
///
/// * `all` → `forall|i: usize| (i < seq.len()) ==> p(seq[i])`
/// * `any` → `exists|i: usize| (i < seq.len()) &&  p(seq[i])`
///
/// The closure body `p(x)` is lowered with the binder `x` substituted by the
/// indexed element `seq[i]`, so the resulting quantifier is structurally the same
/// as the one a hand-written `#[ensures(... forall|i| i < seq.len() ==>
/// p(&seq[i]))]` contract lowers to (the body↔spec link for the `verify_all_*`
/// verdict gate). Returns `Ok(None)` for any receiver that is not a `Seq` or any
/// method other than `all`/`any`, so all other lowering paths are untouched.
fn lower_seq_quantifier_method(
    method: &str,
    mc: &syn::ExprMethodCall,
    receiver_ty: &TrustVcType,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let kind = match method {
        "all" => crate::ir_expr::QuantifierKind::Forall,
        "any" => crate::ir_expr::QuantifierKind::Exists,
        _ => return Ok(None),
    };
    let TrustVcType::Seq(elem_ty) = receiver_ty else {
        return Ok(None);
    };
    let elem_ty = elem_ty.as_ref().clone();
    if mc.args.len() != 1 {
        return Ok(None);
    }
    let syn::Expr::Closure(closure) = &mc.args[0] else {
        return Ok(None);
    };
    if closure.inputs.len() != 1 {
        return Err(LoweringError::UnsupportedExpr(format!(
            "`{method}` over a Seq expects a single-parameter closure, got {}",
            closure.inputs.len()
        )));
    }
    // Extract the (possibly untyped) binder identifier; the element type comes
    // from the Seq, so an explicit annotation is not required here.
    let param_ident = match &closure.inputs[0] {
        syn::Pat::Ident(pi) => pi.ident.clone(),
        syn::Pat::Type(pt) => match pt.pat.as_ref() {
            syn::Pat::Ident(pi) => pi.ident.clone(),
            _ => {
                return Err(LoweringError::UnsupportedPattern(format!(
                    "`{method}` closure parameter must be a plain identifier"
                )))
            }
        },
        _ => {
            return Err(LoweringError::UnsupportedPattern(format!(
                "`{method}` closure parameter must be a plain identifier"
            )))
        }
    };

    // Fresh index binder; depth-suffixed so nested `all/any` do not collide.
    let idx_name = format!("__vc_seq_idx_{depth}");
    let idx_ident = quote::format_ident!("{}", idx_name);
    let base = &mc.receiver;
    // `seq[i]` and `seq.len()` reuse the existing Index / `len()` lowering, so
    // the indexed element and length match the contract's `seq[i]` / `seq.len()`.
    // The element is taken by reference (`&seq[i]`) so the substituted predicate
    // application `eval_constraint(&seq[i], a)` is the SAME term the matching
    // contract `forall|i| .. eval_constraint(&seq[i], a)` lowers to — identical
    // trigger terms are what let ay e-match the body⇔spec quantifier equivalence
    // (a `seq[i]` vs `&seq[i]` arg mismatch would split the two quantifiers into
    // non-cross-instantiable trigger sets and degrade to `Unknown`).
    let index_syn: syn::Expr = syn::parse_quote!(&#base[#idx_ident]);
    let premise_syn: syn::Expr = syn::parse_quote!(#idx_ident < #base.len());

    // Substitute the closure binder with the indexed element inside the body.
    let mut body_syn = (*closure.body).clone();
    let mut subst = SubstituteIdentWithExpr {
        from: param_ident.to_string(),
        to: index_syn,
    };
    syn::visit_mut::VisitMut::visit_expr_mut(&mut subst, &mut body_syn);

    let usize_ty = TrustVcType::Uint {
        width: crate::ir::pointer_width(),
    };
    // Bind the fresh index (usize) and, defensively, the original binder name to
    // the Seq element type — so a stray binder reference the substitution did not
    // reach (e.g. inside a nested closure) still resolves to a concrete type
    // rather than an unbound-variable error.
    let child_env = env.extend(&[
        (idx_name.clone(), usize_ty.clone()),
        (param_ident.to_string(), elem_ty),
    ]);

    let premise = lower_syn_expr_with_depth(&premise_syn, &child_env, depth + 1)?;
    let predicate = lower_syn_expr_with_depth(&body_syn, &child_env, depth + 1)?;

    let body = match kind {
        crate::ir_expr::QuantifierKind::Forall => TrustVcExpr::Implies {
            premise: Box::new(premise),
            conclusion: Box::new(predicate),
        },
        crate::ir_expr::QuantifierKind::Exists => TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(premise),
            right: Box::new(predicate),
        },
    };

    Ok(Some(TrustVcExpr::Quantifier {
        kind,
        bound_vars: vec![(idx_name, usize_ty)],
        body: Box::new(body),
        triggers: None,
        trigger_inference_mode: crate::broadcast_state::get_trigger_inference_mode(),
    }))
}

/// `syn` visitor that replaces every use of a bare identifier with a given
/// expression (used to substitute an `all`/`any` closure binder with the
/// indexed Seq element).
struct SubstituteIdentWithExpr {
    from: String,
    to: syn::Expr,
}

impl syn::visit_mut::VisitMut for SubstituteIdentWithExpr {
    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        if let syn::Expr::Path(path) = expr {
            if path.qself.is_none() && path.path.is_ident(&self.from) {
                *expr = self.to.clone();
                return;
            }
        }
        syn::visit_mut::visit_expr_mut(self, expr);
    }
}

/// The argument index that carries the spec predicate/mapping closure for a
/// ghost-collection combinator op, or `None` for ops that take no spec closure.
///
/// For `filter`/`map`/`map_values`/`flat_map`/`mk_map`/`map_entries`/
/// `filter_keys` the closure is the sole argument (index 0); for the
/// `fold`/`fold_left`/`fold_right` family the initial accumulator is index 0 and
/// the closure is index 1.
fn spec_closure_arg_index(op: &CollectionOp) -> Option<usize> {
    match op {
        CollectionOp::SeqMap
        | CollectionOp::SeqMapValues
        | CollectionOp::SeqFilter
        | CollectionOp::SeqFlatMap
        | CollectionOp::SetFilter
        | CollectionOp::SetMap
        | CollectionOp::SetMkMap
        | CollectionOp::MapMapValues
        | CollectionOp::MapMapEntries
        | CollectionOp::MapFilterKeys => Some(0),
        CollectionOp::SeqFoldLeft | CollectionOp::SeqFoldRight | CollectionOp::SetFold => Some(1),
        _ => None,
    }
}

/// Expected spec-fn parameter types for a combinator closure, derived purely
/// from the receiver type (and, for folds, the already-lowered accumulator
/// argument). Used only as a hint to type untyped closure binders (`|i| ...`);
/// `infer_collection_op_type` re-validates the full `SpecFn` signature, so a
/// wrong or absent hint fails closed rather than admitting an unsound encoding.
fn spec_closure_expected_params(
    op: &CollectionOp,
    receiver_ty: &TrustVcType,
    lowered_args: &[TrustVcExpr],
) -> Option<Vec<TrustVcType>> {
    let usize_ty = TrustVcType::Uint {
        width: crate::ir::pointer_width(),
    };
    match (op, receiver_ty) {
        (CollectionOp::SeqFilter, TrustVcType::Seq(elem))
        | (CollectionOp::SeqMapValues, TrustVcType::Seq(elem))
        | (CollectionOp::SeqFlatMap, TrustVcType::Seq(elem))
        | (CollectionOp::SetFilter, TrustVcType::Set(elem))
        | (CollectionOp::SetMap, TrustVcType::Set(elem))
        | (CollectionOp::SetMkMap, TrustVcType::Set(elem)) => Some(vec![elem.as_ref().clone()]),
        // `Seq::map` passes `(index, element)` to its mapping closure.
        (CollectionOp::SeqMap, TrustVcType::Seq(elem)) => {
            Some(vec![usize_ty, elem.as_ref().clone()])
        }
        (CollectionOp::MapMapValues, TrustVcType::Map(_, val)) => Some(vec![val.as_ref().clone()]),
        (CollectionOp::MapFilterKeys, TrustVcType::Map(key, _)) => Some(vec![key.as_ref().clone()]),
        (CollectionOp::MapMapEntries, TrustVcType::Map(key, val)) => {
            Some(vec![key.as_ref().clone(), val.as_ref().clone()])
        }
        // Folds: accumulator type comes from the already-lowered init (index 0).
        (CollectionOp::SeqFoldLeft, TrustVcType::Seq(elem))
        | (CollectionOp::SetFold, TrustVcType::Set(elem)) => {
            let acc = infer_expr_type(lowered_args.first()?);
            Some(vec![acc, elem.as_ref().clone()])
        }
        (CollectionOp::SeqFoldRight, TrustVcType::Seq(elem)) => {
            let acc = infer_expr_type(lowered_args.first()?);
            Some(vec![elem.as_ref().clone(), acc])
        }
        _ => None,
    }
}

pub(in crate::ir_lowering) fn lower_field_access(
    field: &syn::ExprField,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let receiver = lower_syn_expr_with_depth(&field.base, env, depth)?;
    let receiver_ty = infer_expr_type(&receiver);
    let field_name = match &field.member {
        syn::Member::Named(ident) => ident.to_string(),
        syn::Member::Unnamed(index) => index.index.to_string(),
    };
    let type_name = receiver_ty.to_type_string();
    if let Some(meta) = env.lookup_field(&type_name, &field_name) {
        return Ok(TrustVcExpr::FnCall {
            name: meta.uf_name.clone(),
            args: vec![receiver],
            return_ty: meta.field_type.clone(),
        });
    }
    if let Some((uf_name, field_type)) = field_access_from_receiver_type(&receiver_ty, &field_name)
    {
        return Ok(TrustVcExpr::FnCall {
            name: uf_name,
            args: vec![receiver],
            return_ty: field_type,
        });
    }
    Err(LoweringError::UnsupportedExpr(format!(
        "field '{}' on type '{}'",
        field_name, type_name
    )))
}

pub(in crate::ir_lowering) fn lower_struct_literal(
    expr: &syn::ExprStruct,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    if expr.path.segments.len() > 1 {
        if let Some(meta) = env.resolve_variant_constructor(&expr.path)? {
            let meta = meta.clone();
            return lower_variant_struct_literal(expr, &meta, env, depth);
        }
    }

    let type_name = path_to_string(&expr.path);
    let meta = env.lookup_constructor(&type_name).ok_or_else(|| {
        LoweringError::UnsupportedExpr(format!("struct literal for unknown type '{}'", type_name))
    })?;

    let rest = expr
        .rest
        .as_ref()
        .map(|rest| lower_syn_expr_with_depth(rest, env, depth))
        .transpose()?;
    let rest_ty = rest.as_ref().map(infer_expr_type);
    if let Some(rest_ty) = &rest_ty {
        validate_struct_update_rest_type(&type_name, rest_ty)?;
    }

    let mut seen_fields = BTreeSet::new();
    for field in &expr.fields {
        let field_name = struct_field_name(&field.member);
        if !seen_fields.insert(field_name.clone()) {
            return Err(LoweringError::UnsupportedExpr(format!(
                "duplicate field '{}' in struct literal for '{}'",
                field_name, type_name
            )));
        }
        if !meta
            .fields
            .iter()
            .any(|(expected_name, _)| expected_name == &field_name)
        {
            return Err(LoweringError::UnsupportedExpr(format!(
                "unknown field '{}' in struct literal for '{}'",
                field_name, type_name
            )));
        }
    }

    let mut raw_args = Vec::with_capacity(meta.fields.len());
    let mut type_param_bindings = Vec::new();
    if let Some(TrustVcType::Datatype {
        variants: rest_variants,
        ..
    }) = &rest_ty
    {
        if let [rest_variant] = rest_variants.as_slice() {
            for (field_name, field_type) in &meta.fields {
                if let Some((_, rest_field_ty)) = rest_variant
                    .fields
                    .iter()
                    .find(|(candidate, _)| candidate == field_name)
                {
                    infer_type_param_bindings(field_type, rest_field_ty, &mut type_param_bindings);
                }
            }
        }
    }
    for (field_name, field_type) in &meta.fields {
        if let Some(field) = expr
            .fields
            .iter()
            .find(|candidate| struct_field_name(&candidate.member) == *field_name)
        {
            let lowered = lower_syn_expr_with_depth(&field.expr, env, depth)?;
            let actual_ty = infer_expr_type(&lowered);
            infer_type_param_bindings(field_type, &actual_ty, &mut type_param_bindings);
            raw_args.push(lowered);
        } else if let (Some(rest), Some(rest_ty)) = (rest.as_ref(), rest_ty.as_ref()) {
            let (selector_name, selector_ty) = field_access_from_receiver_type(rest_ty, field_name)
                .ok_or_else(|| {
                    LoweringError::UnsupportedExpr(format!(
                        "missing field '{}' in struct update rest for '{}'",
                        field_name, type_name
                    ))
                })?;
            infer_type_param_bindings(field_type, &selector_ty, &mut type_param_bindings);
            raw_args.push(TrustVcExpr::FnCall {
                name: selector_name,
                args: vec![rest.clone()],
                return_ty: selector_ty,
            });
        } else {
            return Err(LoweringError::UnsupportedExpr(format!(
                "missing field '{}' in struct literal",
                field_name
            )));
        }
    }

    let concrete_fields = meta
        .fields
        .iter()
        .map(|(field_name, field_type)| {
            (
                field_name.clone(),
                substitute_type_params(field_type, &type_param_bindings),
            )
        })
        .collect::<Vec<_>>();
    let args = raw_args
        .into_iter()
        .zip(concrete_fields.iter().map(|(_, ty)| ty))
        .map(|(arg, field_type)| coerce_unsuffixed_literal(arg, field_type))
        .collect::<Vec<_>>();
    let datatype_name = inferred_datatype_name(&type_name, &type_param_bindings);
    let constructor_name = if datatype_name == type_name {
        meta.uf_name.clone()
    } else {
        variant_symbol_name(&datatype_name, &type_name)
    };

    Ok(TrustVcExpr::FnCall {
        name: constructor_name,
        args,
        return_ty: TrustVcType::Datatype {
            name: datatype_name,
            variants: vec![DatatypeVariant::new(type_name, concrete_fields)],
        },
    })
}

fn lower_variant_struct_literal(
    expr: &syn::ExprStruct,
    meta: &DatatypeVariantMeta,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    if expr.rest.is_some() {
        return Err(LoweringError::UnsupportedExpr(format!(
            "struct update syntax for enum variant '{}::{}'",
            meta.datatype_name, meta.variant_name
        )));
    }

    let args = lower_explicit_constructor_fields(
        &format!("{}::{}", meta.datatype_name, meta.variant_name),
        &meta.fields,
        &expr.fields,
        env,
        depth,
    )?;
    Ok(TrustVcExpr::FnCall {
        name: meta.uf_name.clone(),
        args,
        return_ty: meta.return_ty.clone(),
    })
}

fn lower_explicit_constructor_fields(
    constructor_name: &str,
    expected_fields: &[(String, TrustVcType)],
    actual_fields: &syn::punctuated::Punctuated<syn::FieldValue, syn::Token![,]>,
    env: &TypeEnv,
    depth: usize,
) -> Result<Vec<TrustVcExpr>, LoweringError> {
    let mut seen_fields = BTreeSet::new();
    for field in actual_fields {
        let field_name = struct_field_name(&field.member);
        if !seen_fields.insert(field_name.clone()) {
            return Err(LoweringError::UnsupportedExpr(format!(
                "duplicate field '{}' in struct literal for '{}'",
                field_name, constructor_name
            )));
        }
        if !expected_fields
            .iter()
            .any(|(expected_name, _)| expected_name == &field_name)
        {
            return Err(LoweringError::UnsupportedExpr(format!(
                "unknown field '{}' in struct literal for '{}'",
                field_name, constructor_name
            )));
        }
    }

    expected_fields
        .iter()
        .map(|(field_name, field_type)| {
            let field = actual_fields
                .iter()
                .find(|candidate| struct_field_name(&candidate.member) == *field_name)
                .ok_or_else(|| {
                    LoweringError::UnsupportedExpr(format!(
                        "missing field '{}' in struct literal",
                        field_name
                    ))
                })?;
            let lowered = lower_syn_expr_with_depth(&field.expr, env, depth)?;
            Ok(coerce_unsuffixed_literal(lowered, field_type))
        })
        .collect()
}

fn validate_struct_update_rest_type(
    type_name: &str,
    rest_ty: &TrustVcType,
) -> Result<(), LoweringError> {
    let TrustVcType::Datatype { name, variants } = rest_ty else {
        return Err(LoweringError::UnsupportedExpr(format!(
            "struct update rest for '{}' must have the same struct type, got '{}'",
            type_name,
            rest_ty.to_type_string()
        )));
    };
    let [variant] = variants.as_slice() else {
        return Err(LoweringError::UnsupportedExpr(format!(
            "struct update rest for '{}' must be a single-variant struct type, got '{}'",
            type_name,
            rest_ty.to_type_string()
        )));
    };
    if datatype_base_name(name) != type_name || variant.name != type_name {
        return Err(LoweringError::UnsupportedExpr(format!(
            "struct update rest for '{}' must have the same struct type, got '{}'",
            type_name,
            rest_ty.to_type_string()
        )));
    }
    Ok(())
}

pub(super) fn datatype_base_name(name: &str) -> &str {
    name.split('<').next().unwrap_or(name)
}

fn field_access_from_receiver_type(
    receiver_ty: &TrustVcType,
    field_name: &str,
) -> Option<(String, TrustVcType)> {
    let TrustVcType::Datatype { name, variants } = receiver_ty else {
        return None;
    };
    let [variant] = variants.as_slice() else {
        return None;
    };
    let (index, (_, field_ty)) = variant
        .fields
        .iter()
        .enumerate()
        .find(|(_, (candidate, _))| candidate == field_name)?;
    Some((
        selector_symbol_name(name, &variant.name, field_name, index),
        field_ty.clone(),
    ))
}

pub(super) fn inferred_datatype_name(
    type_name: &str,
    bindings: &[(String, TrustVcType)],
) -> String {
    if bindings.is_empty() {
        type_name.to_string()
    } else {
        format!(
            "{}<{}>",
            type_name,
            bindings
                .iter()
                .map(|(_, ty)| ty.to_type_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

pub(super) fn infer_type_param_bindings(
    expected: &TrustVcType,
    actual: &TrustVcType,
    bindings: &mut Vec<(String, TrustVcType)>,
) {
    #[allow(clippy::collapsible_match)]
    match (expected, actual) {
        (TrustVcType::TypeParam(name), ty)
            if !matches!(ty, TrustVcType::TypeParam(_) | TrustVcType::Poly) =>
        {
            if !bindings.iter().any(|(existing, _)| existing == name) {
                bindings.push((name.clone(), ty.clone()));
            }
        }
        (TrustVcType::Seq(expected_inner), TrustVcType::Seq(actual_inner))
        | (TrustVcType::Array(expected_inner, _), TrustVcType::Array(actual_inner, _))
        | (TrustVcType::Set(expected_inner), TrustVcType::Set(actual_inner))
        | (TrustVcType::Multiset(expected_inner), TrustVcType::Multiset(actual_inner)) => {
            infer_type_param_bindings(expected_inner, actual_inner, bindings);
        }
        (
            TrustVcType::Map(expected_key, expected_value),
            TrustVcType::Map(actual_key, actual_value),
        ) => {
            infer_type_param_bindings(expected_key, actual_key, bindings);
            infer_type_param_bindings(expected_value, actual_value, bindings);
        }
        (
            TrustVcType::SpecFn(expected_args, expected_ret),
            TrustVcType::SpecFn(actual_args, actual_ret),
        ) => {
            for (expected_arg, actual_arg) in expected_args.iter().zip(actual_args) {
                infer_type_param_bindings(expected_arg, actual_arg, bindings);
            }
            infer_type_param_bindings(expected_ret, actual_ret, bindings);
        }
        (
            TrustVcType::Datatype {
                variants: expected_variants,
                ..
            },
            TrustVcType::Datatype {
                variants: actual_variants,
                ..
            },
        ) => {
            for (expected_variant, actual_variant) in expected_variants.iter().zip(actual_variants)
            {
                for ((_, expected_field), (_, actual_field)) in expected_variant
                    .fields
                    .iter()
                    .zip(actual_variant.fields.iter())
                {
                    infer_type_param_bindings(expected_field, actual_field, bindings);
                }
            }
        }
        _ => {}
    }
}

pub(crate) fn substitute_type_params(
    ty: &TrustVcType,
    bindings: &[(String, TrustVcType)],
) -> TrustVcType {
    match ty {
        TrustVcType::TypeParam(name) => bindings
            .iter()
            .find_map(|(param, concrete)| (param == name).then(|| concrete.clone()))
            .unwrap_or_else(|| ty.clone()),
        TrustVcType::Seq(inner) => {
            TrustVcType::Seq(Box::new(substitute_type_params(inner, bindings)))
        }
        TrustVcType::Array(inner, len) => {
            TrustVcType::Array(Box::new(substitute_type_params(inner, bindings)), *len)
        }
        TrustVcType::Set(inner) => {
            TrustVcType::Set(Box::new(substitute_type_params(inner, bindings)))
        }
        TrustVcType::Multiset(inner) => {
            TrustVcType::Multiset(Box::new(substitute_type_params(inner, bindings)))
        }
        TrustVcType::Map(key, value) => TrustVcType::Map(
            Box::new(substitute_type_params(key, bindings)),
            Box::new(substitute_type_params(value, bindings)),
        ),
        TrustVcType::SpecFn(args, ret) => TrustVcType::SpecFn(
            args.iter()
                .map(|arg| substitute_type_params(arg, bindings))
                .collect(),
            Box::new(substitute_type_params(ret, bindings)),
        ),
        TrustVcType::Datatype { name, variants } => {
            let substituted_variants: Vec<DatatypeVariant> = variants
                .iter()
                .map(|variant| {
                    DatatypeVariant::new(
                        variant.name.clone(),
                        variant
                            .fields
                            .iter()
                            .map(|(field, field_ty)| {
                                (field.clone(), substitute_type_params(field_ty, bindings))
                            })
                            .collect(),
                    )
                })
                .collect();
            // A tuple carrier derives its datatype NAME structurally from its
            // field types (`(B, A)` -> `(bool, u8)`). After substituting the
            // fields, the name must be recomputed so the per-instantiation tuple
            // carrier matches the structurally-identical tuple the call-site
            // value lowering builds — otherwise a stale template name `(B, A)`
            // (fields already substituted to `bool, u8`) collides with the
            // concrete `(bool, u8)` carrier at datatype registration
            // ("conflicting variant metadata"). Named user datatypes keep their
            // declared name: the recompute is gated on BOTH the sole variant being
            // the anonymous tuple variant AND the carrier name already being a
            // tuple name (starts with `(` — the only shape `tuple_datatype_name`
            // produces), so a hypothetical user enum `enum Foo { Tuple(..) }` is
            // never renamed. (A miss here fails closed on a sort mismatch, never a
            // false verify.)
            let name = match substituted_variants.as_slice() {
                [only]
                    if only.name == crate::ir_expr::TUPLE_VARIANT_NAME && name.starts_with('(') =>
                {
                    crate::ir_expr::tuple_datatype_name(
                        &only
                            .fields
                            .iter()
                            .map(|(_, ty)| ty.clone())
                            .collect::<Vec<_>>(),
                    )
                }
                _ => name.clone(),
            };
            TrustVcType::Datatype {
                name,
                variants: substituted_variants,
            }
        }
        _ => ty.clone(),
    }
}

fn struct_field_name(member: &syn::Member) -> String {
    match member {
        syn::Member::Named(ident) => ident.to_string(),
        syn::Member::Unnamed(index) => index.index.to_string(),
    }
}

fn lower_option_method_call(
    method: &str,
    mc: &syn::ExprMethodCall,
    env: &TypeEnv,
    depth: usize,
    receiver: TrustVcExpr,
    receiver_name: Option<String>,
    receiver_ty: &TrustVcType,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    if !is_option_method(method) {
        return Ok(None);
    }
    let Some(option) = OptionTypeInfo::from_type(receiver_ty) else {
        return Ok(None);
    };
    let known = known_option_binding(&receiver, receiver_name.as_deref(), receiver_ty, env);

    let lowered = match method {
        "is_some" => {
            expect_arg_count(method, mc.args.len(), 0)?;
            match known.as_ref().map(|meta| &meta.state) {
                Some(OptionBindingState::Some { .. }) => TrustVcExpr::BoolLit(true),
                Some(OptionBindingState::None) => TrustVcExpr::BoolLit(false),
                None => option_tester_call(&option, "Some", receiver),
            }
        }
        "is_none" => {
            expect_arg_count(method, mc.args.len(), 0)?;
            match known.as_ref().map(|meta| &meta.state) {
                Some(OptionBindingState::Some { .. }) => TrustVcExpr::BoolLit(false),
                Some(OptionBindingState::None) => TrustVcExpr::BoolLit(true),
                None => option_tester_call(&option, "None", receiver),
            }
        }
        "unwrap" => {
            expect_arg_count(method, mc.args.len(), 0)?;
            if is_erased_ghost_option_view_receiver(&mc.receiver, env) {
                return Ok(Some(option_some_selector(&option, receiver)));
            }
            known_some_value_or_selector(method, receiver, &option, known.as_ref())?
        }
        "expect" => {
            expect_arg_count(method, mc.args.len(), 1)?;
            known_some_value_or_selector(method, receiver, &option, known.as_ref())?
        }
        "unwrap_or_default" => {
            expect_arg_count(method, mc.args.len(), 0)?;
            let default = primitive_numeric_zero(&option.value_ty, method)?;
            lower_option_value_or_else(receiver, &option, known.as_ref(), default)
        }
        "unwrap_or_else" => {
            let fallback_arg = single_method_arg(method, &mc.args)?;
            let fallback = lower_zero_arg_closure_body(method, fallback_arg, env, depth)?;
            let fallback = coerce_unsuffixed_literal(fallback, &option.value_ty);
            lower_option_value_or_else(receiver, &option, known.as_ref(), fallback)
        }
        "ok_or_else" => {
            let fallback_arg = single_method_arg(method, &mc.args)?;
            lower_option_ok_or_else(receiver, &option, known.as_ref(), fallback_arg, env, depth)?
        }
        "and_then" => {
            let closure_arg = single_method_arg(method, &mc.args)?;
            lower_option_and_then(receiver, &option, known.as_ref(), closure_arg, env, depth)?
        }
        "as_mut" => {
            expect_arg_count(method, mc.args.len(), 0)?;
            match known.as_ref().map(|meta| &meta.state) {
                Some(OptionBindingState::None) => receiver,
                Some(OptionBindingState::Some { .. }) | None => {
                    return Err(LoweringError::UnsupportedMethod(
                        "Option::as_mut currently supports only known None observation; \
                         returned mutable references are not modeled"
                            .to_string(),
                    ));
                }
            }
        }
        "cloned" => {
            expect_arg_count(method, mc.args.len(), 0)?;
            receiver
        }
        _ => return Ok(None),
    };

    Ok(Some(lowered))
}

fn is_option_method(method: &str) -> bool {
    matches!(
        method,
        "is_some"
            | "is_none"
            | "unwrap"
            | "expect"
            | "unwrap_or_default"
            | "unwrap_or_else"
            | "ok_or_else"
            | "and_then"
            | "as_mut"
            | "cloned"
    )
}

#[derive(Debug, Clone)]
struct OptionTypeInfo {
    datatype_name: String,
    value_ty: TrustVcType,
}

impl OptionTypeInfo {
    fn from_type(ty: &TrustVcType) -> Option<Self> {
        let TrustVcType::Datatype { name, variants } = ty else {
            return None;
        };
        if !name.starts_with("Option<") {
            return None;
        }
        let value_ty = variants
            .iter()
            .find(|variant| variant.name == "Some")
            .and_then(|variant| variant.fields.first())
            .map(|(_, field_ty)| field_ty.clone())?;
        Some(Self {
            datatype_name: name.clone(),
            value_ty,
        })
    }

    fn datatype_ty(&self) -> TrustVcType {
        option_type(self.value_ty.clone())
    }
}

fn known_option_binding(
    receiver: &TrustVcExpr,
    receiver_name: Option<&str>,
    receiver_ty: &TrustVcType,
    env: &TypeEnv,
) -> Option<OptionBindingMeta> {
    if let Some(meta) = direct_option_binding(receiver) {
        return Some(meta);
    }
    let name = receiver_name?;
    let meta = env.lookup_option_binding(name)?.clone();
    if meta.ty == *receiver_ty {
        Some(meta)
    } else {
        None
    }
}

fn direct_option_binding(expr: &TrustVcExpr) -> Option<OptionBindingMeta> {
    let TrustVcExpr::FnCall {
        name,
        args,
        return_ty,
    } = expr
    else {
        return None;
    };
    let TrustVcType::Datatype {
        name: datatype_name,
        ..
    } = return_ty
    else {
        return None;
    };
    if !datatype_name.starts_with("Option<") {
        return None;
    }
    if name == &variant_symbol_name(datatype_name, "None") && args.is_empty() {
        return Some(OptionBindingMeta {
            ty: return_ty.clone(),
            state: OptionBindingState::None,
        });
    }
    if name == &variant_symbol_name(datatype_name, "Some") && args.len() == 1 {
        return Some(OptionBindingMeta {
            ty: return_ty.clone(),
            state: OptionBindingState::Some {
                value: args.first().cloned(),
            },
        });
    }
    None
}

fn is_erased_ghost_option_view_receiver(receiver: &syn::Expr, env: &TypeEnv) -> bool {
    let syn::Expr::MethodCall(view_call) = unparen_expr(receiver) else {
        return false;
    };
    if view_call.method != "view" || !view_call.args.is_empty() {
        return false;
    }
    direct_path_name(&view_call.receiver)
        .as_deref()
        .is_some_and(|name| env.is_erased_ghost_var(name))
}

fn direct_path_name(expr: &syn::Expr) -> Option<String> {
    match unparen_expr(expr) {
        syn::Expr::Path(path) if path.path.segments.len() == 1 => {
            Some(path.path.segments[0].ident.to_string())
        }
        _ => None,
    }
}

fn unparen_expr(expr: &syn::Expr) -> &syn::Expr {
    let mut current = expr;
    while let syn::Expr::Paren(paren) = current {
        current = &paren.expr;
    }
    current
}

fn expect_arg_count(method: &str, actual: usize, expected: usize) -> Result<(), LoweringError> {
    if actual == expected {
        Ok(())
    } else {
        Err(LoweringError::UnsupportedMethod(format!(
            "{method} expects {expected} arg(s), got {actual}"
        )))
    }
}

fn single_method_arg<'a>(
    method: &str,
    args: &'a syn::punctuated::Punctuated<syn::Expr, syn::Token![,]>,
) -> Result<&'a syn::Expr, LoweringError> {
    expect_arg_count(method, args.len(), 1)?;
    args.first().ok_or_else(|| {
        LoweringError::UnsupportedMethod(format!("{method} expects 1 arg(s), got 0"))
    })
}

/// Lower a Phase C closure reflection method call `f.requires((a, ..))` /
/// `f.ensures((a, ..), r)` on a `SpecFn(arg_tys, ret_ty)` receiver to the opaque
/// Bool UF predicate `call_requires%` / `call_ensures%`.
///
/// The argument list is written as a TUPLE (`(a,)` / `(a, b)`), matching the
/// Verus surface and the definitional axiom co-emitted at the closure literal.
/// The tuple arity must match the `SpecFn` arity; unsuffixed literals are coerced
/// to the parameter / result types. `ensures` takes a trailing `result` argument
/// after the tuple.
fn lower_spec_fn_reflection(
    method: &str,
    mc: &syn::ExprMethodCall,
    receiver: TrustVcExpr,
    arg_tys: &[TrustVcType],
    ret_ty: &TrustVcType,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let is_ensures = method == "ensures";
    let expected_method_args = if is_ensures { 2 } else { 1 };
    if mc.args.len() != expected_method_args {
        return Err(LoweringError::UnsupportedMethod(format!(
            "SpecFn::{method} expects {expected_method_args} argument(s) \
             (an args tuple{}), got {}",
            if is_ensures { " and a result" } else { "" },
            mc.args.len()
        )));
    }

    let syn::Expr::Tuple(tuple) = unparen_expr(&mc.args[0]) else {
        return Err(LoweringError::UnsupportedMethod(format!(
            "SpecFn::{method} expects its arguments as a tuple, e.g. `f.{method}((a,))`"
        )));
    };
    if tuple.elems.len() != arg_tys.len() {
        return Err(LoweringError::UnsupportedMethod(format!(
            "SpecFn::{method} argument-tuple arity {} does not match the closure's {} parameter(s)",
            tuple.elems.len(),
            arg_tys.len()
        )));
    }

    let mut lowered_args = Vec::with_capacity(arg_tys.len());
    for (index, (elem, ty)) in tuple.elems.iter().zip(arg_tys.iter()).enumerate() {
        let lowered = lower_syn_expr_with_depth(elem, env, depth)?;
        let lowered = coerce_unsuffixed_literal(lowered, ty);
        super::calls::require_exact_spec_fn_value_type(
            &lowered,
            ty,
            &format!("SpecFn::{method} argument {index}"),
        )?;
        lowered_args.push(lowered);
    }

    if is_ensures {
        let result = lower_syn_expr_with_depth(&mc.args[1], env, depth)?;
        let result = coerce_unsuffixed_literal(result, ret_ty);
        super::calls::require_exact_spec_fn_value_type(&result, ret_ty, "SpecFn::ensures result")?;
        Ok(crate::ir_builder::call_ensures(
            receiver,
            arg_tys,
            lowered_args,
            result,
            ret_ty,
        ))
    } else {
        Ok(crate::ir_builder::call_requires(
            receiver,
            arg_tys,
            lowered_args,
        ))
    }
}

fn option_tester_call(
    option: &OptionTypeInfo,
    variant: &str,
    receiver: TrustVcExpr,
) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: tester_symbol_name(&option.datatype_name, variant),
        args: vec![receiver],
        return_ty: TrustVcType::Bool,
    }
}

fn known_some_value_or_selector(
    method: &str,
    receiver: TrustVcExpr,
    option: &OptionTypeInfo,
    known: Option<&OptionBindingMeta>,
) -> Result<TrustVcExpr, LoweringError> {
    match known.map(|meta| &meta.state) {
        Some(OptionBindingState::Some { value: Some(value) }) => Ok(value.clone()),
        Some(OptionBindingState::Some { value: None }) => Ok(option_some_selector(option, receiver)),
        Some(OptionBindingState::None) | None => Err(LoweringError::UnsupportedMethod(format!(
            "Option::{method} requires a receiver known to be Some; unsupported receiver fails closed"
        ))),
    }
}

fn option_some_selector(option: &OptionTypeInfo, receiver: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: selector_symbol_name(&option.datatype_name, "Some", "0", 0),
        args: vec![receiver],
        return_ty: option.value_ty.clone(),
    }
}

fn lower_result_method_call(
    method: &str,
    mc: &syn::ExprMethodCall,
    receiver: TrustVcExpr,
    receiver_name: Option<String>,
    receiver_ty: &TrustVcType,
    env: &TypeEnv,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    if !matches!(
        method,
        "is_ok" | "is_err" | "unwrap" | "expect" | "unwrap_err"
    ) {
        return Ok(None);
    }
    let Some(result) = ResultTypeInfo::from_type(receiver_ty) else {
        return Ok(None);
    };
    match method {
        "is_ok" | "is_err" => expect_arg_count(method, mc.args.len(), 0)?,
        "unwrap" => expect_arg_count(method, mc.args.len(), 0)?,
        "expect" => expect_arg_count(method, mc.args.len(), 1)?,
        "unwrap_err" => expect_arg_count(method, mc.args.len(), 0)?,
        _ => unreachable!("guarded above"),
    }
    let known = known_result_binding(&receiver, receiver_name.as_deref(), receiver_ty, env);
    let lowered = match method {
        "is_ok" => match known.as_ref().map(|meta| &meta.state) {
            Some(ResultBindingState::Ok { .. }) => TrustVcExpr::BoolLit(true),
            Some(ResultBindingState::Err { .. }) => TrustVcExpr::BoolLit(false),
            None => result_tester_call(&result, "Ok", receiver),
        },
        "is_err" => match known.as_ref().map(|meta| &meta.state) {
            Some(ResultBindingState::Ok { .. }) => TrustVcExpr::BoolLit(false),
            Some(ResultBindingState::Err { .. }) => TrustVcExpr::BoolLit(true),
            None => result_tester_call(&result, "Err", receiver),
        },
        "unwrap" | "expect" => {
            known_ok_value_or_selector(method, receiver, &result, known.as_ref())?
        }
        "unwrap_err" => known_err_value_or_selector(method, receiver, &result, known.as_ref())?,
        _ => unreachable!("guarded above"),
    };
    Ok(Some(lowered))
}

fn lower_cow_view_method_call(
    method: &str,
    mc: &syn::ExprMethodCall,
    receiver: TrustVcExpr,
    receiver_name: Option<String>,
    receiver_ty: &TrustVcType,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    if method != "view" {
        return Ok(None);
    }
    let Some(inner_ty) = receiver_ty.cow_inner_type() else {
        return Ok(None);
    };
    expect_arg_count(method, mc.args.len(), 0)?;
    let Some(payload) = direct_cow_constructor_payload(&receiver) else {
        return Err(LoweringError::UnsupportedMethod(
            "Cow::view currently requires a direct Cow::Owned(...) or Cow::Borrowed(...) receiver"
                .into(),
        ));
    };
    cow_payload_view(payload, &inner_ty, receiver_name)
        .map(Some)
        .ok_or_else(|| {
            LoweringError::UnsupportedMethod(format!(
                "Cow::view for '{}' is unsupported in this verifier subset",
                inner_ty.to_type_string()
            ))
        })
}

fn direct_cow_constructor_payload(receiver: &TrustVcExpr) -> Option<TrustVcExpr> {
    let TrustVcExpr::FnCall {
        name,
        args,
        return_ty,
    } = receiver
    else {
        return None;
    };
    let TrustVcType::Datatype {
        name: datatype_name,
        ..
    } = return_ty
    else {
        return None;
    };
    if !return_ty.is_cow() || args.len() != 1 {
        return None;
    }
    (name == &variant_symbol_name(datatype_name, "Owned")
        || name == &variant_symbol_name(datatype_name, "Borrowed"))
        .then(|| args.first().cloned())
        .flatten()
}

fn cow_payload_view(
    payload: TrustVcExpr,
    inner_ty: &TrustVcType,
    receiver_name: Option<String>,
) -> Option<TrustVcExpr> {
    let payload_ty = infer_expr_type(&payload);
    if let Some(view_ty) = payload_ty.view_collection_type() {
        return Some(TrustVcExpr::CollectionOp {
            op: CollectionOp::View,
            receiver_name: lowered_receiver_name(&payload).or(receiver_name),
            receiver: Box::new(payload),
            args: vec![],
            ty: view_ty,
        });
    }

    if &payload_ty != inner_ty {
        return None;
    }
    let (uf_name, field_ty) = single_field_view_selector(&payload_ty)?;
    Some(TrustVcExpr::FnCall {
        name: uf_name,
        args: vec![payload],
        return_ty: field_ty,
    })
}

fn single_field_view_selector(ty: &TrustVcType) -> Option<(String, TrustVcType)> {
    let TrustVcType::Datatype { variants, .. } = ty else {
        return None;
    };
    let [variant] = variants.as_slice() else {
        return None;
    };
    let [(field_name, _)] = variant.fields.as_slice() else {
        return None;
    };
    field_access_from_receiver_type(ty, field_name)
}

#[derive(Debug, Clone)]
struct ResultTypeInfo {
    datatype_name: String,
    ok_ty: TrustVcType,
    err_ty: TrustVcType,
}

impl ResultTypeInfo {
    fn from_type(ty: &TrustVcType) -> Option<Self> {
        let TrustVcType::Datatype { name, variants } = ty else {
            return None;
        };
        if !name.starts_with("Result<") {
            return None;
        }
        let ok_ty = variants
            .iter()
            .find(|variant| variant.name == "Ok")
            .and_then(|variant| variant.fields.first())
            .map(|(_, field_ty)| field_ty.clone())?;
        let err_ty = variants
            .iter()
            .find(|variant| variant.name == "Err")
            .and_then(|variant| variant.fields.first())
            .map(|(_, field_ty)| field_ty.clone())?;
        Some(Self {
            datatype_name: name.clone(),
            ok_ty,
            err_ty,
        })
    }
}

fn known_result_binding(
    receiver: &TrustVcExpr,
    receiver_name: Option<&str>,
    receiver_ty: &TrustVcType,
    env: &TypeEnv,
) -> Option<ResultBindingMeta> {
    if let Some(meta) = direct_result_binding(receiver) {
        return Some(meta);
    }
    let name = receiver_name?;
    let meta = env.lookup_result_binding(name)?.clone();
    if meta.ty == *receiver_ty {
        Some(meta)
    } else {
        None
    }
}

fn direct_result_binding(expr: &TrustVcExpr) -> Option<ResultBindingMeta> {
    let TrustVcExpr::FnCall {
        name,
        args,
        return_ty,
    } = expr
    else {
        return None;
    };
    let TrustVcType::Datatype {
        name: datatype_name,
        ..
    } = return_ty
    else {
        return None;
    };
    if !datatype_name.starts_with("Result<") {
        return None;
    }
    if is_direct_result_variant_constructor(name, datatype_name, "Ok") && args.len() == 1 {
        return Some(ResultBindingMeta {
            ty: return_ty.clone(),
            state: ResultBindingState::Ok {
                value: args.first().cloned(),
            },
        });
    }
    if is_direct_result_variant_constructor(name, datatype_name, "Err") && args.len() == 1 {
        return Some(ResultBindingMeta {
            ty: return_ty.clone(),
            state: ResultBindingState::Err {
                error: args.first().cloned(),
            },
        });
    }
    None
}

fn is_direct_result_variant_constructor(name: &str, datatype_name: &str, variant: &str) -> bool {
    name == variant_symbol_name(datatype_name, variant)
}

fn known_ok_value_or_selector(
    method: &str,
    receiver: TrustVcExpr,
    result: &ResultTypeInfo,
    known: Option<&ResultBindingMeta>,
) -> Result<TrustVcExpr, LoweringError> {
    match known.map(|meta| &meta.state) {
        Some(ResultBindingState::Ok { value: Some(value) }) => Ok(value.clone()),
        Some(ResultBindingState::Ok { value: None }) => Ok(result_ok_selector(result, receiver)),
        Some(ResultBindingState::Err { .. }) | None => {
            Err(LoweringError::UnsupportedMethod(format!(
                "Result::{method} requires a receiver known to be Ok; unsupported receiver fails closed"
            )))
        }
    }
}

fn result_ok_selector(result: &ResultTypeInfo, receiver: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: selector_symbol_name(&result.datatype_name, "Ok", "0", 0),
        args: vec![receiver],
        return_ty: result.ok_ty.clone(),
    }
}

fn result_tester_call(
    result: &ResultTypeInfo,
    variant: &str,
    receiver: TrustVcExpr,
) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: tester_symbol_name(&result.datatype_name, variant),
        args: vec![receiver],
        return_ty: TrustVcType::Bool,
    }
}

fn known_err_value_or_selector(
    method: &str,
    receiver: TrustVcExpr,
    result: &ResultTypeInfo,
    known: Option<&ResultBindingMeta>,
) -> Result<TrustVcExpr, LoweringError> {
    match known.map(|meta| &meta.state) {
        Some(ResultBindingState::Err { error: Some(error) }) => Ok(error.clone()),
        Some(ResultBindingState::Err { error: None }) => Ok(result_err_selector(result, receiver)),
        Some(ResultBindingState::Ok { .. }) | None => {
            Err(LoweringError::UnsupportedMethod(format!(
                "Result::{method} requires a receiver known to be Err; unsupported receiver fails closed"
            )))
        }
    }
}

fn result_err_selector(result: &ResultTypeInfo, receiver: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: selector_symbol_name(&result.datatype_name, "Err", "0", 0),
        args: vec![receiver],
        return_ty: result.err_ty.clone(),
    }
}

/// Structural equality of two `Result` values: both `Ok` with equal payloads, or
/// both `Err` with equal payloads. Sound only when BOTH payload types are
/// structural-eq (the caller restricts to integer `Ok`/`Err`), so the selector
/// comparisons are structural. Mirrors `option_structural_eq_expr`.
fn result_structural_eq_expr(
    result: &ResultTypeInfo,
    left: TrustVcExpr,
    right: TrustVcExpr,
) -> TrustVcExpr {
    let and3 = |a, b, c| TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(a),
            right: Box::new(b),
        }),
        right: Box::new(c),
    };
    let both_ok = and3(
        result_tester_call(result, "Ok", left.clone()),
        result_tester_call(result, "Ok", right.clone()),
        compare_expr(
            CompareOp::Eq,
            result_ok_selector(result, left.clone()),
            result_ok_selector(result, right.clone()),
        ),
    );
    let both_err = and3(
        result_tester_call(result, "Err", left.clone()),
        result_tester_call(result, "Err", right.clone()),
        compare_expr(
            CompareOp::Eq,
            result_err_selector(result, left),
            result_err_selector(result, right),
        ),
    );
    TrustVcExpr::Logic {
        op: LogicOp::Or,
        left: Box::new(both_ok),
        right: Box::new(both_err),
    }
}

fn primitive_numeric_zero(ty: &TrustVcType, method: &str) -> Result<TrustVcExpr, LoweringError> {
    if matches!(ty, TrustVcType::Int { .. } | TrustVcType::Uint { .. }) {
        Ok(TrustVcExpr::IntLit {
            value: 0,
            ty: ty.clone(),
        })
    } else {
        Err(LoweringError::UnsupportedMethod(format!(
            "Option::{method} is supported only for primitive integer defaults, got '{}'",
            ty.to_type_string()
        )))
    }
}

fn lower_option_value_or_else(
    receiver: TrustVcExpr,
    option: &OptionTypeInfo,
    known: Option<&OptionBindingMeta>,
    fallback: TrustVcExpr,
) -> TrustVcExpr {
    match known.map(|meta| &meta.state) {
        Some(OptionBindingState::Some { value: Some(value) }) => value.clone(),
        Some(OptionBindingState::Some { value: None }) => option_some_selector(option, receiver),
        Some(OptionBindingState::None) => fallback,
        None => TrustVcExpr::Match {
            scrutinee: Box::new(receiver),
            arms: vec![
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "Some".to_string(),
                        bindings: vec!["__trust_vc_option_value".to_string()],
                        has_rest: false,
                    },
                    TrustVcExpr::Var {
                        name: "__trust_vc_option_value".to_string(),
                        ty: option.value_ty.clone(),
                    },
                ),
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "None".to_string(),
                        bindings: vec![],
                        has_rest: false,
                    },
                    fallback,
                ),
            ],
            ty: option.value_ty.clone(),
        },
    }
}

fn lower_option_ok_or_else(
    receiver: TrustVcExpr,
    option: &OptionTypeInfo,
    known: Option<&OptionBindingMeta>,
    fallback_arg: &syn::Expr,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let err_expr = lower_zero_arg_closure_body("ok_or_else", fallback_arg, env, depth)?;
    let err_ty = infer_expr_type(&err_expr);
    let result_ty = result_type(option.value_ty.clone(), err_ty.clone());
    let ok_from_value = |value: TrustVcExpr| -> Result<TrustVcExpr, LoweringError> {
        datatype_constructor_expr(&result_ty, "Ok", vec![value])
    };
    let err_expr = coerce_unsuffixed_literal(err_expr, &err_ty);
    let err_constructor = datatype_constructor_expr(&result_ty, "Err", vec![err_expr])?;

    match known.map(|meta| &meta.state) {
        Some(OptionBindingState::Some { value: Some(value) }) => ok_from_value(value.clone()),
        Some(OptionBindingState::Some { value: None }) => {
            ok_from_value(option_some_selector(option, receiver))
        }
        Some(OptionBindingState::None) => Ok(err_constructor),
        None => Ok(TrustVcExpr::Match {
            scrutinee: Box::new(receiver),
            arms: vec![
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "Some".to_string(),
                        bindings: vec!["__trust_vc_option_ok".to_string()],
                        has_rest: false,
                    },
                    datatype_constructor_expr(
                        &result_ty,
                        "Ok",
                        vec![TrustVcExpr::Var {
                            name: "__trust_vc_option_ok".to_string(),
                            ty: option.value_ty.clone(),
                        }],
                    )?,
                ),
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "None".to_string(),
                        bindings: vec![],
                        has_rest: false,
                    },
                    err_constructor,
                ),
            ],
            ty: result_ty,
        }),
    }
}

fn lower_option_and_then(
    receiver: TrustVcExpr,
    option: &OptionTypeInfo,
    known: Option<&OptionBindingMeta>,
    closure_arg: &syn::Expr,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let closure = parse_option_closure_arg(closure_arg, "and_then")?;
    let (param_name, param_ty) = extract_unary_closure_param(&closure, "and_then", env)?;
    if param_ty != option.value_ty {
        return Err(LoweringError::TypeInference(format!(
            "Option::and_then closure parameter must be '{}', got '{}'",
            option.value_ty.to_type_string(),
            param_ty.to_type_string()
        )));
    }
    let body = lower_closure_body_with_bindings(
        &closure,
        env,
        depth,
        &[(param_name.clone(), param_ty.clone())],
        None,
    )?;
    let result_option = OptionTypeInfo::from_type(&infer_expr_type(&body)).ok_or_else(|| {
        LoweringError::TypeInference(format!(
            "Option::and_then closure must return Option<_>, got '{}'",
            infer_expr_type(&body).to_type_string()
        ))
    })?;
    let result_ty = result_option.datatype_ty();
    let none_result = datatype_constructor_expr(&result_ty, "None", vec![])?;

    let apply_to = |value: TrustVcExpr| TrustVcExpr::Let {
        name: param_name.clone(),
        ty: param_ty.clone(),
        value: Box::new(value),
        body: Box::new(body.clone()),
    };

    match known.map(|meta| &meta.state) {
        Some(OptionBindingState::Some { value: Some(value) }) => Ok(apply_to(value.clone())),
        Some(OptionBindingState::Some { value: None }) => {
            Ok(apply_to(option_some_selector(option, receiver)))
        }
        Some(OptionBindingState::None) => Ok(none_result),
        None => Ok(TrustVcExpr::Match {
            scrutinee: Box::new(receiver),
            arms: vec![
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "Some".to_string(),
                        bindings: vec![param_name],
                        has_rest: false,
                    },
                    body,
                ),
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "None".to_string(),
                        bindings: vec![],
                        has_rest: false,
                    },
                    none_result,
                ),
            ],
            ty: result_ty,
        }),
    }
}

fn lower_zero_arg_closure_body(
    method: &str,
    closure_arg: &syn::Expr,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let closure = parse_option_closure_arg(closure_arg, method)?;
    if closure.input_len() != 0 {
        return Err(LoweringError::UnsupportedMethod(format!(
            "Option fallback closure expects 0 parameters, got {}",
            closure.input_len()
        )));
    }
    lower_closure_body_with_bindings(&closure, env, depth, &[], None)
}

fn extract_unary_closure_param(
    closure: &OptionClosureArg<'_>,
    method: &str,
    env: &TypeEnv,
) -> Result<(String, TrustVcType), LoweringError> {
    closure.unary_typed_ident(method, env)
}

fn lower_closure_body_with_bindings(
    closure: &OptionClosureArg<'_>,
    env: &TypeEnv,
    depth: usize,
    bindings: &[(String, TrustVcType)],
    expected_ty: Option<&TrustVcType>,
) -> Result<TrustVcExpr, LoweringError> {
    let child_env = env.extend(bindings);
    let mut body = lower_syn_expr_with_depth(closure.body(), &child_env, depth)?;
    let annotation_ty = closure
        .output_type()
        .map(|ty| env.resolve_syn_type(ty))
        .transpose()?;
    if let Some(ty) = expected_ty.or(annotation_ty.as_ref()) {
        body = coerce_unsuffixed_literal(body, ty);
    }
    Ok(body)
}

fn option_type(inner_ty: TrustVcType) -> TrustVcType {
    TrustVcType::Datatype {
        name: format!("Option<{}>", inner_ty.to_type_string()),
        variants: vec![
            DatatypeVariant::new("None", vec![]),
            DatatypeVariant::new("Some", vec![("0".to_string(), inner_ty)]),
        ],
    }
}

fn result_type(ok_ty: TrustVcType, err_ty: TrustVcType) -> TrustVcType {
    TrustVcType::Datatype {
        name: format!(
            "Result<{}, {}>",
            ok_ty.to_type_string(),
            err_ty.to_type_string()
        ),
        variants: vec![
            DatatypeVariant::new("Ok", vec![("0".to_string(), ok_ty)]),
            DatatypeVariant::new("Err", vec![("0".to_string(), err_ty)]),
        ],
    }
}

fn datatype_constructor_expr(
    datatype_ty: &TrustVcType,
    variant: &str,
    args: Vec<TrustVcExpr>,
) -> Result<TrustVcExpr, LoweringError> {
    let TrustVcType::Datatype { name, variants } = datatype_ty else {
        return Err(LoweringError::InvalidType(
            "datatype constructor helper requires a datatype".into(),
        ));
    };
    let Some(meta) = variants.iter().find(|candidate| candidate.name == variant) else {
        return Err(LoweringError::InvalidType(format!(
            "datatype '{}' has no '{}' variant",
            name, variant
        )));
    };
    if meta.fields.len() != args.len() {
        return Err(LoweringError::TypeInference(format!(
            "constructor '{}' expects {} argument(s), got {}",
            variant,
            meta.fields.len(),
            args.len()
        )));
    }
    let coerced_args = args
        .into_iter()
        .zip(meta.fields.iter())
        .map(|(arg, (_, field_ty))| coerce_unsuffixed_literal(arg, field_ty))
        .collect();
    Ok(TrustVcExpr::FnCall {
        name: variant_symbol_name(name, variant),
        args: coerced_args,
        return_ty: datatype_ty.clone(),
    })
}

/// Map Rust method name to IR wrapping mode + arithmetic op.
///
/// Note: `checked_*` maps to overflow-checked arithmetic (not `Option<T>`).
/// See [`WrappingMode::Checked`] for the semantics gap (#1785).
fn match_wrapping_method(m: &str) -> Option<(WrappingMode, ArithOp)> {
    Some(match m {
        "wrapping_add" => (WrappingMode::Wrapping, ArithOp::Add),
        "wrapping_sub" => (WrappingMode::Wrapping, ArithOp::Sub),
        "wrapping_mul" => (WrappingMode::Wrapping, ArithOp::Mul),
        "checked_add" => (WrappingMode::Checked, ArithOp::Add),
        "checked_sub" => (WrappingMode::Checked, ArithOp::Sub),
        "checked_mul" => (WrappingMode::Checked, ArithOp::Mul),
        "saturating_add" => (WrappingMode::Saturating, ArithOp::Add),
        "saturating_sub" => (WrappingMode::Saturating, ArithOp::Sub),
        "saturating_mul" => (WrappingMode::Saturating, ArithOp::Mul),
        _ => return None,
    })
}

fn lower_primitive_integer_trait_method_call(
    method: &str,
    mc: &syn::ExprMethodCall,
    env: &TypeEnv,
    depth: usize,
    receiver: TrustVcExpr,
    receiver_ty: &TrustVcType,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    // `core::ops::Shl::shl` / `core::ops::Shr::shr` method-call form. These map
    // to the *same* `SpecialArith { op: Shl/Shr, .. }` IR as the binary `<<`/`>>`
    // operators (see `ir_lowering/operators.rs:114-115`), so they reuse the
    // already-verified sound shift-overflow checker (`encode_bv_shift`, which
    // fails closed when the amount `>= width`). The shift amount may be any
    // finite integer type — matching Rust/Verus, where the RHS type of a shift
    // need not equal the LHS — and `encode_bv_shift` enforces the in-range bound
    // regardless. Part of #2779 (upstream `operators.rs` `test_arith`).
    if let Some(shift_op) = match method {
        "shl" => Some(SpecialArithOp::Shl),
        "shr" => Some(SpecialArithOp::Shr),
        _ => None,
    } {
        if !receiver_ty.is_integer() {
            return Ok(None);
        }
        if mc.args.len() != 1 {
            return Err(LoweringError::UnsupportedMethod(format!(
                "{method} expects 1 arg, got {}",
                mc.args.len()
            )));
        }
        let Some(arg) = mc.args.first() else {
            unreachable!("guarded: len == 1")
        };
        let lowered_arg = lower_syn_expr_with_depth(arg, env, depth)?;
        // Coerce an unsuffixed literal shift amount to the receiver's integer
        // type so it carries a known width; an already-suffixed amount of a
        // different integer type is preserved (the shift encoder coerces widths
        // and fails closed on out-of-range amounts).
        let lowered_arg = coerce_unsuffixed_literal(lowered_arg, receiver_ty);
        let arg_ty = infer_expr_type(&lowered_arg);
        if !arg_ty.is_integer() {
            return Err(LoweringError::UnsupportedMethod(format!(
                "{method}() on `{}` requires an integer shift amount, got `{}`",
                receiver_ty.to_type_string(),
                arg_ty.to_type_string()
            )));
        }
        return Ok(Some(TrustVcExpr::SpecialArith {
            op: shift_op,
            left: Box::new(receiver),
            right: Box::new(lowered_arg),
            ty: receiver_ty.clone(),
        }));
    }

    let op = match method {
        "add" => ArithOp::Add,
        _ => return Ok(None),
    };
    if mc.args.len() != 1 {
        return Err(LoweringError::UnsupportedMethod(format!(
            "{method} expects 1 arg, got {}",
            mc.args.len()
        )));
    }
    if !receiver_ty.is_integer() {
        return Ok(None);
    }

    let Some(arg) = mc.args.first() else {
        unreachable!("guarded: len == 1")
    };
    let lowered_arg = lower_syn_expr_with_depth(arg, env, depth)?;
    let lowered_arg = coerce_unsuffixed_literal(lowered_arg, receiver_ty);
    let arg_ty = infer_expr_type(&lowered_arg);
    if arg_ty != *receiver_ty {
        return Err(LoweringError::UnsupportedMethod(format!(
            "{method}() on `{}` requires an argument of the same finite integer type, got `{}`",
            receiver_ty.to_type_string(),
            arg_ty.to_type_string()
        )));
    }

    Ok(Some(arith_expr(
        op,
        receiver,
        lowered_arg,
        receiver_ty.clone(),
    )))
}

fn lower_partial_ord_integer_method_call(
    method: &str,
    mc: &syn::ExprMethodCall,
    env: &TypeEnv,
    depth: usize,
    receiver: TrustVcExpr,
    receiver_ty: &TrustVcType,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let op = match method {
        "lt" => CompareOp::Lt,
        "le" => CompareOp::Le,
        "gt" => CompareOp::Gt,
        "ge" => CompareOp::Ge,
        _ => return Ok(None),
    };
    if mc.args.len() != 1 {
        return Err(LoweringError::UnsupportedMethod(format!(
            "{method} expects 1 arg, got {}",
            mc.args.len()
        )));
    }
    if !receiver_ty.is_integer() {
        if !env.source_type_shadows_builtin("Option") {
            if let Some(option) = OptionTypeInfo::from_type(receiver_ty) {
                // `option_partial_ord_expr` models all four orderings for a totally
                // ordered `Option<T>` (integer T): the strict `Lt`/`Gt` directly and
                // the reflexive `Le`/`Ge` as `lt || eq` / `!lt`.
                return lower_partial_ord_option_method_call(
                    method,
                    op,
                    mc,
                    env,
                    depth,
                    receiver,
                    receiver_ty,
                    &option,
                );
            }
        }
        return Err(LoweringError::UnsupportedMethod(format!(
            "{method}() is currently unsupported for type `{}`; PartialOrd integer methods require a finite-width integer receiver",
            receiver_ty.to_type_string()
        )));
    }

    let Some(arg) = mc.args.first() else {
        unreachable!("guarded: len == 1")
    };
    let lowered_arg = lower_syn_expr_with_depth(arg, env, depth)?;
    let arg_ty = infer_expr_type(&lowered_arg);
    let left = coerce_unsuffixed_literal(receiver, &arg_ty);
    let right = coerce_unsuffixed_literal(lowered_arg, receiver_ty);
    let left_ty = infer_expr_type(&left);
    let right_ty = infer_expr_type(&right);
    if !right_ty.is_integer() || left_ty != right_ty {
        return Err(LoweringError::UnsupportedMethod(format!(
            "{method}() on `{}` requires an argument of the same finite integer type, got `{}`",
            left_ty.to_type_string(),
            right_ty.to_type_string()
        )));
    }

    Ok(Some(compare_expr(op, left, right)))
}

/// A type whose `==` is UNCONDITIONALLY the structural SMT equality, so `.eq()`
/// desugars to `==` soundly: the primitives (integer/bool/char) plus a TUPLE all
/// of whose components are themselves structural-eq. A tuple can never carry a
/// user `PartialEq` impl, BUT its derived `PartialEq` compares component-wise via
/// each component's `PartialEq` — so a tuple containing a custom-`PartialEq` type
/// is NOT structural and is excluded (recursively). A plain datatype/struct is
/// excluded (it may carry a non-structural custom `PartialEq`).
fn is_canonical_tuple_carrier(name: &str, variants: &[crate::ir::DatatypeVariant]) -> bool {
    matches!(
        variants,
        [only]
            if only.name == crate::ir_expr::TUPLE_VARIANT_NAME
                && only
                    .fields
                    .iter()
                    .enumerate()
                    .all(|(index, (field, _))| field == &index.to_string())
                && name
                    == crate::ir_expr::tuple_datatype_name(
                        &only
                            .fields
                            .iter()
                            .map(|(_, field_ty)| field_ty.clone())
                            .collect::<Vec<_>>(),
                    )
    )
}

fn is_canonical_option_carrier(
    name: &str,
    variants: &[crate::ir::DatatypeVariant],
    env: &TypeEnv,
) -> bool {
    !env.source_type_shadows_builtin("Option")
        && matches!(
            variants,
            [none, some]
                if none.name == "None"
                    && none.fields.is_empty()
                    && some.name == "Some"
                    && matches!(some.fields.as_slice(), [(field, _)] if field == "0")
                    && name == format!("Option<{}>", some.fields[0].1.to_type_string())
        )
}

fn is_canonical_result_carrier(
    name: &str,
    variants: &[crate::ir::DatatypeVariant],
    env: &TypeEnv,
) -> bool {
    !env.source_type_shadows_builtin("Result")
        && matches!(
            variants,
            [ok, err]
                if ok.name == "Ok"
                    && err.name == "Err"
                    && matches!(ok.fields.as_slice(), [(field, _)] if field == "0")
                    && matches!(err.fields.as_slice(), [(field, _)] if field == "0")
                    && name
                        == format!(
                            "Result<{}, {}>",
                            ok.fields[0].1.to_type_string(),
                            err.fields[0].1.to_type_string()
                        )
        )
}

fn datatype_payloads_are(
    variants: &[crate::ir::DatatypeVariant],
    mut predicate: impl FnMut(&TrustVcType) -> bool,
) -> bool {
    variants.iter().all(|variant| {
        variant
            .fields
            .iter()
            .all(|(_, field_ty)| predicate(field_ty))
    })
}

fn is_structural_eq_type(ty: &TrustVcType, env: &TypeEnv) -> bool {
    if ty.is_integer() {
        return true;
    }
    match ty {
        TrustVcType::Bool | TrustVcType::Char => true,
        TrustVcType::Datatype { name, variants } => {
            // A complete canonical tuple/builtin carrier, or a source datatype
            // with an authoritative `#[derive(PartialEq)]` record, is structural
            // exactly when every payload is structural recursively. A user type
            // cannot spoof tuple/Option/Result semantics from names alone, while
            // a genuinely derived source `Option` remains supported via its
            // derive record even though it shadows the builtin.
            let structural_carrier = is_canonical_tuple_carrier(name, variants)
                || is_canonical_option_carrier(name, variants, env)
                || is_canonical_result_carrier(name, variants, env)
                || env.has_derived_partial_eq(name);
            structural_carrier
                && datatype_payloads_are(variants, |field_ty| is_structural_eq_type(field_ty, env))
        }
        _ => false,
    }
}

/// A type whose `Clone` is a structural value-copy, so `x.clone()` reduces to
/// `x`: primitives (including `Copy` floats), canonical tuples/std
/// Option/Result, and source datatypes carrying `#[derive(Clone)]`, recursively
/// over payloads. Clone and PartialEq derive provenance are intentionally
/// independent.
fn is_structural_clone_type(ty: &TrustVcType, env: &TypeEnv) -> bool {
    if ty.is_integer()
        || matches!(
            ty,
            TrustVcType::Bool | TrustVcType::Char | TrustVcType::Float { width: 32 | 64 }
        )
    {
        return true;
    }
    match ty {
        TrustVcType::Datatype { name, variants } => {
            let structural_carrier = is_canonical_tuple_carrier(name, variants)
                || is_canonical_option_carrier(name, variants, env)
                || is_canonical_result_carrier(name, variants, env)
                || env.has_derived_clone(name);
            structural_carrier
                && datatype_payloads_are(variants, |field_ty| {
                    is_structural_clone_type(field_ty, env)
                })
        }
        _ => false,
    }
}

/// Lowers the `PartialEq` methods `.eq(&other)` / `.ne(&other)` to the structural
/// spec equality `==` / `!=` — but ONLY for receivers whose `==` IS the structural
/// SMT equality ([`is_structural_eq_type`]: primitives + tuples of structural
/// components), matching Verus. A user type may carry a NON-structural custom
/// `PartialEq` impl (row 382's keystone side), so desugaring its `.eq()` to a
/// structural `==` the impl contradicts would be a false-verify; those decline
/// (fall through) and stay fail-closed. Mirrors `lower_partial_ord_integer_method_call`
/// (which handles `lt`/`le`/`gt`/`ge` for the analogous structural-order case).
fn lower_partial_eq_method_call(
    method: &str,
    mc: &syn::ExprMethodCall,
    env: &TypeEnv,
    depth: usize,
    receiver: TrustVcExpr,
    receiver_ty: &TrustVcType,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let op = match method {
        "eq" => CompareOp::Eq,
        "ne" => CompareOp::Ne,
        _ => return Ok(None),
    };
    // DECLINE (fall through) for anything that is not a clean primitive same-type
    // `.eq`/`.ne` — this handler only ever ADDS the primitive case; non-primitive
    // receivers (custom PartialEq, collections with their own `.eq` handlers) keep
    // their existing behavior (a downstream handler, or the final fail-closed
    // unsupported-method error). Never a hard error here, so nothing is preempted.
    if mc.args.len() != 1 {
        return Ok(None);
    }
    // `Option<integer>`: structural equality via the same encoder the ordering
    // methods (`.lt/.le/.gt/.ge`) use. Restricted to an integer value type so the
    // payload comparison IS structural — an `Option<CustomType>` would compare the
    // payload with the custom `PartialEq` and is declined (fall through).
    if !env.source_type_shadows_builtin("Option") {
        if let Some(option) = OptionTypeInfo::from_type(receiver_ty) {
            if option.value_ty.is_integer() {
                let arg = single_method_arg(method, &mc.args)?;
                let lowered_arg = lower_syn_expr_with_depth(arg, env, depth)?;
                if infer_expr_type(&lowered_arg) == *receiver_ty {
                    let eq = option_structural_eq_expr(&option, receiver, lowered_arg);
                    return Ok(Some(match op {
                        CompareOp::Ne => TrustVcExpr::Not(Box::new(eq)),
                        _ => eq,
                    }));
                }
            }
            return Ok(None);
        }
    }
    // `Result<integer, integer>`: structural equality of both payloads. Same
    // structural-payload restriction as the Option case.
    if !env.source_type_shadows_builtin("Result") {
        if let Some(result) = ResultTypeInfo::from_type(receiver_ty) {
            if result.ok_ty.is_integer() && result.err_ty.is_integer() {
                let arg = single_method_arg(method, &mc.args)?;
                let lowered_arg = lower_syn_expr_with_depth(arg, env, depth)?;
                if infer_expr_type(&lowered_arg) == *receiver_ty {
                    let eq = result_structural_eq_expr(&result, receiver, lowered_arg);
                    return Ok(Some(match op {
                        CompareOp::Ne => TrustVcExpr::Not(Box::new(eq)),
                        _ => eq,
                    }));
                }
            }
            return Ok(None);
        }
    }
    if !is_structural_eq_type(receiver_ty, env) {
        return Ok(None);
    }

    let Some(arg) = mc.args.first() else {
        unreachable!("guarded: len == 1")
    };
    let lowered_arg = lower_syn_expr_with_depth(arg, env, depth)?;
    // Integer receivers coerce an unsuffixed literal to the receiver's type (mirror
    // the ordering path); bool/char take the operands verbatim.
    let (left, right) = if receiver_ty.is_integer() {
        let arg_ty = infer_expr_type(&lowered_arg);
        (
            coerce_unsuffixed_literal(receiver, &arg_ty),
            coerce_unsuffixed_literal(lowered_arg, receiver_ty),
        )
    } else {
        (receiver, lowered_arg)
    };
    // Different operand types → decline (structural `==` requires a common type);
    // fall through rather than fabricate a comparison across mismatched sorts.
    if infer_expr_type(&left) != infer_expr_type(&right) {
        return Ok(None);
    }

    Ok(Some(compare_expr(op, left, right)))
}

/// Lowers the finite-width-integer `Ord`/sign methods `max`, `min`, `abs`, and
/// `saturating_abs` to their sound `if/else` (`Ite`) desugarings over the
/// already-supported comparison / arithmetic IR, so spec/body lowering can model
/// the real `(rhs.saturating_sub(lhs)).max(0)` and
/// `lhs.saturating_sub(rhs).saturating_abs()` constructs without a hand-written
/// twin. Returns `Ok(None)` for any other method so the dispatcher keeps trying
/// the remaining lowering paths.
///
/// Soundness of each desugaring (matching Rust's documented semantics exactly):
/// * `a.max(b)  === if a >= b { a } else { b }`
/// * `a.min(b)  === if a <= b { a } else { b }`
/// * `x.abs()   === if x < 0 { 0 - x } else { x }` — for finite-width signed `x`
///   this is total only when `x != MIN` (Rust panics / is UB-on-overflow at
///   `MIN`); we therefore fail closed for the panicking case via the
///   already-overflow-checked `Sub` encoding, so an `abs` that could overflow
///   does not verify (more conservative than Rust, never less).
/// * `x.saturating_abs()` matches Rust precisely, including the `i128::MIN`
///   corner: `if x == MIN { MAX } else if x < 0 { 0 - x } else { x }`. For
///   `x != MIN`, `0 - x` cannot overflow, so the plain `Sub` is total here.
///
/// Unsigned receivers: `max`/`min` are modeled (unsigned ordering); `abs`/
/// `saturating_abs` are not unsigned methods and fall through to the normal
/// unsupported-method diagnostic.
fn lower_minmax_abs_integer_method_call(
    method: &str,
    mc: &syn::ExprMethodCall,
    env: &TypeEnv,
    depth: usize,
    receiver: TrustVcExpr,
    receiver_ty: &TrustVcType,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    enum Kind {
        Max,
        Min,
        Abs,
        SaturatingAbs,
    }
    let kind = match method {
        "max" => Kind::Max,
        "min" => Kind::Min,
        "abs" => Kind::Abs,
        "saturating_abs" => Kind::SaturatingAbs,
        _ => return Ok(None),
    };

    if !receiver_ty.is_integer() {
        // Let non-integer receivers (e.g. collection/user-defined `max`) flow to
        // the remaining dispatch paths instead of claiming them here.
        return Ok(None);
    }
    let ty = receiver_ty.clone();

    match kind {
        Kind::Max | Kind::Min => {
            let arg = single_method_arg(method, &mc.args)?;
            let lowered_arg = lower_syn_expr_with_depth(arg, env, depth)?;
            let lowered_arg = coerce_unsuffixed_literal(lowered_arg, &ty);
            let arg_ty = infer_expr_type(&lowered_arg);
            if arg_ty != ty {
                return Err(LoweringError::UnsupportedMethod(format!(
                    "{method}() on `{}` requires an argument of the same finite integer type, got `{}`",
                    ty.to_type_string(),
                    arg_ty.to_type_string()
                )));
            }
            let cmp = if matches!(kind, Kind::Max) {
                CompareOp::Ge
            } else {
                CompareOp::Le
            };
            // a.max(b) === if a >= b { a } else { b }
            // a.min(b) === if a <= b { a } else { b }
            Ok(Some(ite_expr(
                compare_expr(cmp, receiver.clone(), lowered_arg.clone()),
                receiver,
                lowered_arg,
                ty,
            )))
        }
        Kind::Abs | Kind::SaturatingAbs => {
            expect_arg_count(method, mc.args.len(), 0)?;
            if receiver_ty.is_unsigned() {
                // `abs`/`saturating_abs` are signed-integer methods; an unsigned
                // receiver should fall through to the standard diagnostic.
                return Ok(None);
            }
            let zero = integer_lit(0, ty.clone());
            // 0 - x  (negation as a subtraction so it reuses the overflow-checked
            // `Sub` encoding; for x != MIN this is total).
            let neg = arith_expr(ArithOp::Sub, zero.clone(), receiver.clone(), ty.clone());
            let is_negative = compare_expr(CompareOp::Lt, receiver.clone(), zero);
            let core_abs = ite_expr(is_negative, neg, receiver.clone(), ty.clone());
            if matches!(kind, Kind::Abs) {
                return Ok(Some(core_abs));
            }
            // x.saturating_abs() === if x == MIN { MAX } else { abs(x) }.
            // Spelling MIN/MAX via the same finite-width int literals the body
            // uses keeps the i128::MIN saturation corner exact.
            let (min_value, max_value) = signed_min_max(&ty).ok_or_else(|| {
                LoweringError::UnsupportedMethod(format!(
                    "saturating_abs() on `{}` requires a fixed-width signed integer",
                    ty.to_type_string()
                ))
            })?;
            let is_min = compare_expr(CompareOp::Eq, receiver, integer_lit(min_value, ty.clone()));
            Ok(Some(ite_expr(
                is_min,
                integer_lit(max_value, ty.clone()),
                core_abs,
                ty,
            )))
        }
    }
}

/// Returns `(MIN, MAX)` for a fixed-width signed integer type as `i128` values,
/// or `None` for `i128` itself (whose `MIN`/`MAX` do not fit in `i128` symmetric
/// helpers — handled directly) and non-signed-finite types.
///
/// `i128` is supported explicitly: `i128::MIN`/`i128::MAX` are exactly
/// representable in `i128`, so we return them. Widths above 128 are unsupported.
fn signed_min_max(ty: &TrustVcType) -> Option<(i128, i128)> {
    let TrustVcType::Int { width } = ty else {
        return None;
    };
    let width = *width;
    if width == 0 || width > 128 {
        return None;
    }
    if width == 128 {
        return Some((i128::MIN, i128::MAX));
    }
    // For width w < 128: MIN = -(1 << (w-1)), MAX = (1 << (w-1)) - 1.
    let half = 1i128 << (width - 1);
    Some((-half, half - 1))
}

// The pre-derived `option` view is threaded alongside `receiver_ty` to avoid
// re-deriving it at the single call site; the parameters are cohesive lowering
// inputs and splitting them into a wrapper struct would not aid readability.
#[allow(clippy::too_many_arguments)]
fn lower_partial_ord_option_method_call(
    method: &str,
    op: CompareOp,
    mc: &syn::ExprMethodCall,
    env: &TypeEnv,
    depth: usize,
    receiver: TrustVcExpr,
    receiver_ty: &TrustVcType,
    option: &OptionTypeInfo,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    if !option.value_ty.is_integer() {
        return Err(LoweringError::UnsupportedMethod(format!(
            "{method}() on `{}` currently supports only Option<T> with a finite-width integer T",
            receiver_ty.to_type_string()
        )));
    }

    let arg = single_method_arg(method, &mc.args)?;
    let lowered_arg = lower_syn_expr_with_depth(arg, env, depth)?;
    let arg_ty = infer_expr_type(&lowered_arg);
    if arg_ty != *receiver_ty {
        return Err(LoweringError::UnsupportedMethod(format!(
            "{method}() on `{}` requires an argument of the same Option type, got `{}`",
            receiver_ty.to_type_string(),
            arg_ty.to_type_string()
        )));
    }

    Ok(Some(option_partial_ord_expr(
        op,
        option,
        receiver,
        lowered_arg,
    )))
}

fn option_partial_ord_expr(
    op: CompareOp,
    option: &OptionTypeInfo,
    left: TrustVcExpr,
    right: TrustVcExpr,
) -> TrustVcExpr {
    match op {
        CompareOp::Lt => option_lt_expr(option, left, right),
        CompareOp::Gt => TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(TrustVcExpr::Not(Box::new(option_lt_expr(
                option,
                left.clone(),
                right.clone(),
            )))),
            right: Box::new(TrustVcExpr::Not(Box::new(option_structural_eq_expr(
                option, left, right,
            )))),
        },
        // `a <= b` iff `a < b || a == b` (total order over Option<integer>).
        CompareOp::Le => TrustVcExpr::Logic {
            op: LogicOp::Or,
            left: Box::new(option_lt_expr(option, left.clone(), right.clone())),
            right: Box::new(option_structural_eq_expr(option, left, right)),
        },
        // `a >= b` iff `!(a < b)` (total order — `lt` and `eq`/`gt` partition).
        CompareOp::Ge => TrustVcExpr::Not(Box::new(option_lt_expr(option, left, right))),
        _ => TrustVcExpr::BoolLit(false),
    }
}

fn option_lt_expr(option: &OptionTypeInfo, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    let left_some = option_tester_call(option, "Some", left.clone());
    let left_none = option_tester_call(option, "None", left.clone());
    let right_some = option_tester_call(option, "Some", right.clone());
    let value_cmp = compare_expr(
        CompareOp::Lt,
        option_some_selector(option, left),
        option_some_selector(option, right),
    );

    ite_expr(
        left_none,
        right_some.clone(),
        ite_expr(
            left_some,
            TrustVcExpr::Logic {
                op: LogicOp::And,
                left: Box::new(right_some),
                right: Box::new(value_cmp),
            },
            TrustVcExpr::BoolLit(false),
            TrustVcType::Bool,
        ),
        TrustVcType::Bool,
    )
}

fn option_structural_eq_expr(
    option: &OptionTypeInfo,
    left: TrustVcExpr,
    right: TrustVcExpr,
) -> TrustVcExpr {
    let left_none = option_tester_call(option, "None", left.clone());
    let right_none = option_tester_call(option, "None", right.clone());
    let left_some = option_tester_call(option, "Some", left.clone());
    let right_some = option_tester_call(option, "Some", right.clone());
    let value_eq = compare_expr(
        CompareOp::Eq,
        option_some_selector(option, left),
        option_some_selector(option, right),
    );

    TrustVcExpr::Logic {
        op: LogicOp::Or,
        left: Box::new(TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(left_none),
            right: Box::new(right_none),
        }),
        right: Box::new(TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(left_some),
            right: Box::new(TrustVcExpr::Logic {
                op: LogicOp::And,
                left: Box::new(right_some),
                right: Box::new(value_eq),
            }),
        }),
    }
}

/// Lowers `a.min(b)` / `a.max(b)` on an integer receiver to the defining
/// conditional, the exact semantics of `Ord::min`/`Ord::max` on integers:
///
/// * `a.min(b)` → `if a <= b { a } else { b }`
/// * `a.max(b)` → `if a >= b { a } else { b }`
///
/// Supported for finite-width integers (`i128`, `u32`, …) and for the Verus
/// mathematical integers `int`/`nat`. `min`/`max` never overflow, so no
/// finite-width sign correction is needed — the lowering is a pure `Ite` over the
/// receiver type's comparison. This unblocks specifying the ay-pb cutting-planes
/// `impliedGe_saturate` step (refutation_check.rs:176, `c.min(self.rhs)`) verbatim
/// over the kernel's ℤ algebra, where the SATURATION rule soundness is stated.
/// Returns `Ok(None)` for a non-integer receiver so other handlers can report.
fn lower_minmax_integer_method_call(
    method: &str,
    mc: &syn::ExprMethodCall,
    env: &TypeEnv,
    depth: usize,
    receiver: TrustVcExpr,
    receiver_ty: &TrustVcType,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    if !matches!(method, "min" | "max") {
        return Ok(None);
    }
    let receiver_is_integer =
        receiver_ty.is_integer() || matches!(receiver_ty, TrustVcType::MathInt | TrustVcType::Nat);
    if !receiver_is_integer {
        return Ok(None);
    }
    if mc.args.len() != 1 {
        return Err(LoweringError::UnsupportedMethod(format!(
            "{method} expects 1 arg, got {}",
            mc.args.len()
        )));
    }

    let Some(arg) = mc.args.first() else {
        unreachable!("guarded: len == 1")
    };
    let lowered_arg = lower_syn_expr_with_depth(arg, env, depth)?;
    let lowered_arg = coerce_unsuffixed_literal(lowered_arg, receiver_ty);
    let arg_ty = infer_expr_type(&lowered_arg);

    // The argument must share the receiver's integer sort. For `int`/`nat` allow
    // either mathematical-integer sort (they share the SMT `Int` sort); for a
    // finite-width receiver require the identical width/signedness so the BV
    // comparison is well-typed.
    let arg_is_compatible = match receiver_ty {
        TrustVcType::MathInt | TrustVcType::Nat => {
            matches!(arg_ty, TrustVcType::MathInt | TrustVcType::Nat)
        }
        _ => arg_ty == *receiver_ty,
    };
    if !arg_is_compatible {
        return Err(LoweringError::UnsupportedMethod(format!(
            "{method}() on `{}` requires an argument of the same integer type, got `{}`",
            receiver_ty.to_type_string(),
            arg_ty.to_type_string()
        )));
    }

    // `min` keeps the receiver when `a <= b`; `max` keeps it when `a >= b`.
    let cmp = if method == "min" {
        CompareOp::Le
    } else {
        CompareOp::Ge
    };
    let cond = compare_expr(cmp, receiver.clone(), lowered_arg.clone());
    Ok(Some(TrustVcExpr::Ite {
        cond: Box::new(cond),
        then_branch: Box::new(receiver),
        else_branch: Box::new(lowered_arg),
        ty: receiver_ty.clone(),
    }))
}

fn lower_euclidean_integer_method_call(
    method: &str,
    mc: &syn::ExprMethodCall,
    env: &TypeEnv,
    depth: usize,
    receiver: TrustVcExpr,
    receiver_ty: &TrustVcType,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    if !matches!(method, "div_euclid" | "rem_euclid") {
        return Ok(None);
    }
    if mc.args.len() != 1 {
        return Err(LoweringError::UnsupportedMethod(format!(
            "{method} expects 1 arg, got {}",
            mc.args.len()
        )));
    }

    let Some(arg) = mc.args.first() else {
        unreachable!("guarded: len == 1")
    };
    let lowered_arg = lower_syn_expr_with_depth(arg, env, depth)?;
    let lowered_arg = coerce_unsuffixed_literal(lowered_arg, receiver_ty);
    let arg_ty = infer_expr_type(&lowered_arg);

    // Verus mathematical integers (`int`/`nat`): the SMT-LIB `Int` `div`/`mod`
    // the encoder emits for `ArithOp::Div`/`Rem` are DEFINED with Euclidean
    // semantics (`a = b*(a div b) + (a mod b)` with `0 <= a mod b < |b|`; see
    // `encoder::ir_encoder::arith::int_arith` `is_math_integer` arms and
    // `int_euclidean_div`/`int_euclidean_mod`). That is exactly Rust's
    // `int::div_euclid` / `rem_euclid` over the unbounded integers, so route the
    // methods straight to `Div`/`Rem` with NO finite-width sign-correction
    // wrapper (unlike the signed finite path below). This unblocks specifying the
    // ay-pb cutting-planes `ceil_div` helper (refutation_check.rs:206-217, built
    // from `checked_div_euclid`/`checked_rem_euclid`) over the kernel's ℤ algebra,
    // where the rule soundness is stated (the i128 checker's `checked_*` ops
    // reject any overflowing step, so each accepted step's arithmetic is this ℤ
    // arithmetic). Matches the `/`/`%` operator lowering, which is already
    // Euclidean for `int` (see encoder tests `compute_euclidean_int_div`).
    if matches!(receiver_ty, TrustVcType::MathInt | TrustVcType::Nat) {
        if !matches!(arg_ty, TrustVcType::MathInt | TrustVcType::Nat) {
            return Err(LoweringError::UnsupportedMethod(format!(
                "{method}() on `{}` requires an `int`/`nat` argument, got `{}`",
                receiver_ty.to_type_string(),
                arg_ty.to_type_string()
            )));
        }
        let op = if method == "div_euclid" {
            ArithOp::Div
        } else {
            ArithOp::Rem
        };
        return Ok(Some(arith_expr(
            op,
            receiver,
            lowered_arg,
            receiver_ty.clone(),
        )));
    }

    if !receiver_ty.is_integer() {
        return Err(LoweringError::UnsupportedMethod(format!(
            "{method}() is currently unsupported for type `{}`; Euclidean integer methods require a finite-width integer or `int`/`nat` receiver",
            receiver_ty.to_type_string()
        )));
    }
    if arg_ty != *receiver_ty {
        return Err(LoweringError::UnsupportedMethod(format!(
            "{method}() on `{}` requires an argument of the same finite integer type, got `{}`",
            receiver_ty.to_type_string(),
            arg_ty.to_type_string()
        )));
    }

    if receiver_ty.is_unsigned() {
        let op = if method == "div_euclid" {
            ArithOp::Div
        } else {
            ArithOp::Rem
        };
        return Ok(Some(arith_expr(
            op,
            receiver,
            lowered_arg,
            receiver_ty.clone(),
        )));
    }

    Ok(Some(lower_signed_euclidean_integer_method(
        method,
        receiver,
        lowered_arg,
        receiver_ty.clone(),
    )))
}

fn lower_signed_euclidean_integer_method(
    method: &str,
    receiver: TrustVcExpr,
    rhs: TrustVcExpr,
    ty: TrustVcType,
) -> TrustVcExpr {
    let trunc_div = arith_expr(ArithOp::Div, receiver.clone(), rhs.clone(), ty.clone());
    let trunc_rem = arith_expr(ArithOp::Rem, receiver, rhs.clone(), ty.clone());
    let rem_is_negative =
        compare_expr(CompareOp::Lt, trunc_rem.clone(), integer_lit(0, ty.clone()));

    if method == "div_euclid" {
        let rhs_is_positive = compare_expr(CompareOp::Gt, rhs, integer_lit(0, ty.clone()));
        let decrement = arith_expr(
            ArithOp::Sub,
            trunc_div.clone(),
            integer_lit(1, ty.clone()),
            ty.clone(),
        );
        let increment = arith_expr(
            ArithOp::Add,
            trunc_div.clone(),
            integer_lit(1, ty.clone()),
            ty.clone(),
        );
        return ite_expr(
            rem_is_negative,
            ite_expr(rhs_is_positive, decrement, increment, ty.clone()),
            trunc_div,
            ty,
        );
    }

    let rhs_is_negative = compare_expr(CompareOp::Lt, rhs.clone(), integer_lit(0, ty.clone()));
    let subtract_rhs = arith_expr(ArithOp::Sub, trunc_rem.clone(), rhs.clone(), ty.clone());
    let add_rhs = arith_expr(ArithOp::Add, trunc_rem.clone(), rhs, ty.clone());
    ite_expr(
        rem_is_negative,
        ite_expr(rhs_is_negative, subtract_rhs, add_rhs, ty.clone()),
        trunc_rem,
        ty,
    )
}

fn integer_lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}

fn arith_expr(op: ArithOp, left: TrustVcExpr, right: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

fn compare_expr(op: CompareOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn ite_expr(
    cond: TrustVcExpr,
    then_branch: TrustVcExpr,
    else_branch: TrustVcExpr,
    ty: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::Ite {
        cond: Box::new(cond),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
        ty,
    }
}

fn lower_prophecy_method_call(
    method: &str,
    receiver_name: Option<&str>,
    args: &syn::punctuated::Punctuated<syn::Expr, syn::Token![,]>,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(name) = receiver_name else {
        return Ok(None);
    };
    let Some(inner_ty) = env.lookup_prophecy(name).cloned() else {
        return Ok(None);
    };

    let lowered = match method {
        "view" => {
            if !args.is_empty() {
                return Err(LoweringError::UnsupportedMethod(format!(
                    "prophecy view expects 0 args, got {}",
                    args.len()
                )));
            }
            TrustVcExpr::ProphecyNew {
                name: name.to_string(),
                ty: inner_ty,
            }
        }
        "resolve" => {
            if args.len() != 1 {
                return Err(LoweringError::UnsupportedMethod(format!(
                    "prophecy resolve expects 1 arg, got {}",
                    args.len()
                )));
            }
            TrustVcExpr::ProphecyResolve {
                name: name.to_string(),
                value: Box::new(lower_syn_expr_with_depth(&args[0], env, depth)?),
            }
        }
        _ => return Ok(None),
    };

    Ok(Some(lowered))
}

#[cfg(feature = "native-strings")]
fn lower_native_string_method_call(
    method: &str,
    mc: &syn::ExprMethodCall,
    env: &TypeEnv,
    depth: usize,
    receiver: TrustVcExpr,
    receiver_name: Option<String>,
    receiver_ty: &TrustVcType,
) -> Result<TrustVcExpr, LoweringError> {
    match method {
        "view" => {
            if !mc.args.is_empty() {
                return Err(LoweringError::UnsupportedMethod(format!(
                    "view expects 0 args, got {}",
                    mc.args.len()
                )));
            }
            let view_ty = receiver_ty.view_collection_type().ok_or_else(|| {
                LoweringError::TypeInference(format!(
                    "view() on '{}' should expose a Seq<char> view",
                    receiver_ty.to_type_string()
                ))
            })?;
            Ok(TrustVcExpr::CollectionOp {
                op: CollectionOp::View,
                receiver: Box::new(receiver),
                receiver_name,
                args: vec![],
                ty: view_ty,
            })
        }
        "len" => {
            if !mc.args.is_empty() {
                return Err(LoweringError::UnsupportedMethod(format!(
                    "len expects 0 args, got {}",
                    mc.args.len()
                )));
            }
            Ok(TrustVcExpr::CollectionOp {
                op: CollectionOp::Len,
                receiver: Box::new(receiver),
                receiver_name,
                args: vec![],
                ty: TrustVcType::Uint {
                    width: crate::ir::pointer_width(),
                },
            })
        }
        "contains" => lower_native_string_predicate(
            method,
            mc,
            env,
            depth,
            receiver,
            receiver_name,
            receiver_ty,
            None,
        ),
        "starts_with" => lower_native_string_predicate(
            method,
            mc,
            env,
            depth,
            receiver,
            receiver_name,
            receiver_ty,
            Some(crate::ir_expr::NATIVE_STRING_STARTS_WITH_FN),
        ),
        "ends_with" => lower_native_string_predicate(
            method,
            mc,
            env,
            depth,
            receiver,
            receiver_name,
            receiver_ty,
            Some(crate::ir_expr::NATIVE_STRING_ENDS_WITH_FN),
        ),
        _ => Err(LoweringError::UnsupportedMethod(format!(
            "{} on '{}' is not yet supported under native-strings",
            method,
            receiver_ty.to_type_string()
        ))),
    }
}

#[cfg(feature = "native-strings")]
fn lower_native_string_predicate(
    method: &str,
    mc: &syn::ExprMethodCall,
    env: &TypeEnv,
    depth: usize,
    receiver: TrustVcExpr,
    receiver_name: Option<String>,
    receiver_ty: &TrustVcType,
    native_fn_name: Option<&str>,
) -> Result<TrustVcExpr, LoweringError> {
    if mc.args.len() != 1 {
        return Err(LoweringError::UnsupportedMethod(format!(
            "{} expects 1 arg, got {}",
            method,
            mc.args.len()
        )));
    }

    let arg = lower_syn_expr_with_depth(&mc.args[0], env, depth)?;
    let arg_ty = infer_expr_type(&arg);
    if !arg_ty.is_string_like() {
        return Err(LoweringError::TypeInference(format!(
            "{} on '{}' requires a String/str argument, got '{}'",
            method,
            receiver_ty.to_type_string(),
            arg_ty.to_type_string()
        )));
    }

    if method == "contains" {
        return Ok(TrustVcExpr::CollectionOp {
            op: CollectionOp::Contains,
            receiver: Box::new(receiver),
            receiver_name,
            args: vec![arg],
            ty: TrustVcType::Bool,
        });
    }

    let native_fn_name = native_fn_name.ok_or_else(|| {
        LoweringError::UnsupportedMethod(format!(
            "{method} requires a native string helper function name"
        ))
    })?;

    Ok(TrustVcExpr::FnCall {
        name: native_fn_name.to_string(),
        args: vec![receiver, arg],
        return_ty: TrustVcType::Bool,
    })
}

#[cfg(test)]
mod structural_eq_type_tests {
    use super::is_structural_eq_type;
    use crate::ir::{DatatypeVariant, TrustVcType};
    use crate::ir_lowering::TypeEnv;

    fn u64_ty() -> TrustVcType {
        TrustVcType::Uint { width: 64 }
    }

    #[test]
    fn canonical_tuple_identity_is_required_for_structural_equality() {
        let env = TypeEnv::new();
        let canonical = crate::ir_expr::tuple_datatype_type(vec![u64_ty(), TrustVcType::Bool]);
        assert!(is_structural_eq_type(&canonical, &env));

        let user_datatype_with_tuple_variant = TrustVcType::Datatype {
            name: "UserTupleName".to_string(),
            variants: vec![DatatypeVariant::new(
                crate::ir_expr::TUPLE_VARIANT_NAME,
                vec![("0".to_string(), u64_ty())],
            )],
        };
        assert!(!is_structural_eq_type(
            &user_datatype_with_tuple_variant,
            &env
        ));

        let noncanonical_fields = TrustVcType::Datatype {
            name: "(u64,)".to_string(),
            variants: vec![DatatypeVariant::new(
                crate::ir_expr::TUPLE_VARIANT_NAME,
                vec![("payload".to_string(), u64_ty())],
            )],
        };
        assert!(!is_structural_eq_type(&noncanonical_fields, &env));
    }
}
