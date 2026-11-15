//! Function-call lowering helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2526.

use super::super::{
    expr_path_to_string, infer_expr_type, integer_positions_agree, lower_syn_expr_with_depth,
    operators::coerce_unsuffixed_literal, trust_vc_type_from_syn_type_with_env,
    type_holds_an_integer, LoweringError, TypeEnv, SOURCE_CATALOG_MATH_INT_MARKER,
};
use super::collections::lower_collection_constructor;
use super::macros::{lower_choose, lower_quantifier};
use super::methods::{datatype_base_name, infer_type_param_bindings, substitute_type_params};
use super::spec_closure::{lower_spec_fn_arg, lower_spec_fn_new};
use crate::encoder::datatype::{selector_symbol_name, variant_symbol_name};
use crate::ir::{DatatypeVariant, TrustVcType};
use crate::ir_expr::{
    ArithOp, CollectionOp, CompareOp, LogicOp, QuantifierKind, TrustVcExpr, WrappingMode,
};

pub(super) fn require_exact_spec_fn_value_type(
    expr: &TrustVcExpr,
    expected: &TrustVcType,
    context: &str,
) -> Result<(), LoweringError> {
    let actual = infer_expr_type(expr);
    if &actual == expected {
        return Ok(());
    }
    Err(LoweringError::TypeInference(format!(
        "{context} has type `{}`, expected `{}`",
        actual.to_type_string(),
        expected.to_type_string(),
    )))
}

pub(in crate::ir_lowering) fn lower_call(
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    if let syn::Expr::Path(path) = &*call.func {
        if path.path.segments.len() == 1
            && matches!(
                path.path.segments[0].ident.to_string().as_str(),
                "Some" | "Ok" | "Err"
            )
        {
            crate::ir_lowering::entry::refuse_unsuffixed_float_elements(
                call.args.iter(),
                "an `Option` or `Result` payload",
            )?;
        }
        if path_matches_suffix(&path.path, &["SpecFn", "new"]) {
            return lower_spec_fn_new(call, env, depth);
        }
        if let Some(size_of) = lower_core_mem_size_of_call(path, call, env)? {
            return Ok(size_of);
        }
        if let Some(align_of) = lower_core_mem_align_of_call(path, call, env)? {
            return Ok(align_of);
        }
        if let Some(from_fn) = lower_seq_from_fn_call(path, call, env, depth)? {
            return Ok(from_fn);
        }
        if let Some(set_new) = lower_set_new_call(path, call, env, depth)? {
            return Ok(set_new);
        }
        if path_matches_suffix(&path.path, &["Proph", "new"]) {
            return lower_prophecy_new_call(path, call, env);
        }
        // Phase C closure reflection, free-fn surface:
        // `call_requires(f, (a, ..))` / `call_ensures(f, (a, ..), r)` — the
        // parallel of the `f.requires(..)` / `f.ensures(..)` method form.
        if let Some(reflection) = lower_closure_reflection_free_fn(path, call, env, depth)? {
            return Ok(reflection);
        }
        // `Box::new(x)` / `Rc::new(x)` / `Arc::new(x)` are transparent ownership/heap
        // wrappers with no ghost-level meaning. The IR models datatype recursion
        // DIRECTLY via `RecursiveRef` (a recursive field declared `Box<Nat>` carries
        // a bare `Nat`), so the boxed payload IS the value: lower the sole argument
        // and return it unchanged. This mirrors the transparent `*box` deref already
        // handled during extraction and is what lets `Succ(Box::new(Zero))` lower to
        // the `Succ` constructor applied to a `Nat`.
        if call.args.len() == 1
            && (path_matches_suffix(&path.path, &["Box", "new"])
                || path_matches_suffix(&path.path, &["Rc", "new"])
                || path_matches_suffix(&path.path, &["Arc", "new"]))
        {
            // The payload's type is the wrapper's type parameter: an
            // unsuffixed float literal there is the untyped float, never the
            // exact `real` (`*Box::new(0.1) + 0.2 == 0.3` was `Verified`).
            crate::ir_lowering::entry::refuse_unsuffixed_float_elements(
                call.args.iter(),
                "a `Box`, `Rc` or `Arc` payload",
            )?;
            return lower_syn_expr_with_depth(&call.args[0], env, depth);
        }
        if call.args.is_empty() {
            if let Some(constructor) = lower_collection_constructor(path, env)? {
                return Ok(constructor);
            }
        }
        if call.args.len() == 1 {
            if let Some(singleton_expr) = lower_collection_singleton(path, call, env, depth)? {
                return Ok(singleton_expr);
            }
        }
        if let Some(bound) = lower_let_bound_marker(path, call, env, depth)? {
            return Ok(bound);
        }
        if let Some(bound) = lower_bind_like_marker(path, call, env, depth)? {
            return Ok(bound);
        }
        if let Some(value) = lower_self_typed_marker(path, call, env, depth)? {
            return Ok(value);
        }
        if let Some(value) =
            super::super::untyped_site::lower_untyped_site_marker(path, call, env, depth)?
        {
            return Ok(value);
        }
        if let Some(value) =
            super::super::untyped_site::lower_untyped_binding_marker(path, call, env, depth)?
        {
            return Ok(value);
        }
        if let Some(value) =
            super::super::untyped_site::lower_slot_typed_marker(path, call, env, depth)?
        {
            return Ok(value);
        }
        let name = expr_path_to_string(path);
        if let Some(refusal) = mut_ref_vocabulary_refusal(&name) {
            return Err(LoweringError::UnsupportedExpr(refusal));
        }
        if name == SOURCE_CATALOG_MATH_INT_MARKER {
            if !env.allows_source_catalog_math_int_marker() {
                return Err(LoweringError::UnsupportedExpr(
                    "reserved source-catalog math-int marker outside its authenticated obligation"
                        .into(),
                ));
            }
            if call.args.len() != 1 {
                return Err(LoweringError::TypeInference(format!(
                    "internal math-int expression marker expects 1 argument, got {}",
                    call.args.len()
                )));
            }
            let lowered = lower_syn_expr_with_depth(&call.args[0], env, depth)?;
            return promote_result_expr_to_math_int(lowered);
        }
        if name == "forall" || name == "exists" {
            let kind = if name == "forall" {
                QuantifierKind::Forall
            } else {
                QuantifierKind::Exists
            };
            return lower_quantifier(kind, call, env, depth);
        }
        if name == "choose" {
            return lower_choose(call, env, depth);
        }
        if let Some(ordering) = lower_decreases_ordering_call(&name, call, env, depth)? {
            return Ok(ordering);
        }
        if let Some(constructor) = lower_explicit_builtin_constructor_call(path, call, env, depth)?
        {
            return Ok(constructor);
        }
        if let Some(default_value) = lower_default_constructor_call(path, call, env, depth)? {
            return Ok(default_value);
        }
        if let Some(projection) = lower_result_projection_shim_call(&name, call, env, depth)? {
            return Ok(projection);
        }
        if let Some(projection) = lower_field_projection_shim_call(&name, call, env, depth)? {
            return Ok(projection);
        }
        if let Some(constructor) = lower_cow_constructor_call(path, call, env, depth)? {
            return Ok(constructor);
        }
        if let Some(constructor) = lower_inferred_some_constructor_call(path, call, env, depth)? {
            return Ok(constructor);
        }
        if let Some(meta) = env.resolve_variant_constructor(&path.path)? {
            // Lower the constructor arguments once up front. Lowering does not
            // depend on the (not-yet-computed) type-param bindings — only the
            // final literal coercion does — so we can use the lowered argument
            // types to infer the bindings for a generic recursive datatype
            // constructor written WITHOUT a turbofish (e.g. `GCons(5i32, GNil)`).
            let raw_args: Vec<_> = call
                .args
                .iter()
                .map(|arg| lower_syn_expr_with_depth(arg, env, depth))
                .collect::<Result<Vec<_>, LoweringError>>()?;

            let mut type_param_bindings = explicit_constructor_type_arg_bindings(path, meta, env)?;
            // Argument-driven monomorphization for a SELF-RECURSIVE generic
            // carrier whose type arguments were left implicit (no turbofish):
            // bind each field `TypeParam` from the corresponding lowered
            // argument's type, so `GCons(5i32, ..)` binds `T -> i32` and the
            // constructed value lands in the per-instantiation carrier
            // `GList<i32>` (concrete field sorts, self-only `RecursiveRef`),
            // exactly as a builtin `List<i32>` already does. Gated to recursive
            // carriers so the non-recursive generic-struct path (#2778, driven
            // by an explicit turbofish) keeps its byte-identical behavior.
            if type_param_bindings.is_empty() && carrier_is_self_recursive(&meta.return_ty) {
                for ((_, field_ty), arg) in meta.fields.iter().zip(raw_args.iter()) {
                    infer_type_param_bindings(
                        field_ty,
                        &infer_expr_type(arg),
                        &mut type_param_bindings,
                    );
                }
            }

            let fields = meta
                .fields
                .iter()
                .map(|(field_name, field_ty)| {
                    (
                        field_name.clone(),
                        substitute_type_params(field_ty, &type_param_bindings),
                    )
                })
                .collect::<Vec<_>>();
            let return_ty = substitute_constructor_return_ty(&meta.return_ty, &type_param_bindings);
            if fields.len() != call.args.len() {
                return Err(LoweringError::TypeInference(format!(
                    "constructor '{}' expects {} argument(s), got {}",
                    meta.variant_name,
                    fields.len(),
                    call.args.len(),
                )));
            }
            let args: Vec<_> = raw_args
                .into_iter()
                .zip(fields.iter())
                .map(|(lowered, (_, field_ty))| coerce_unsuffixed_literal(lowered, field_ty))
                .collect();
            let name = if type_param_bindings.is_empty() {
                meta.uf_name.clone()
            } else if let TrustVcType::Datatype { name, .. } = &return_ty {
                variant_symbol_name(name, &meta.variant_name)
            } else {
                meta.uf_name.clone()
            };
            return Ok(TrustVcExpr::FnCall {
                name,
                args,
                return_ty,
            });
        }
        if let Some(trait_call) = lower_concrete_trait_path_call(&name, path, call, env, depth)? {
            return Ok(trait_call);
        }
        // Phase C part 2: DIRECT APPLICATION `f(a, b, ..)` of a first-class
        // `SpecFn` value. A single-name callee that resolves to a `SpecFn`-typed
        // variable is a closure VALUE (a `let f = trust_vc::closure!(..)` literal,
        // or a `SpecFn` parameter). For an ARITY-N `Fn(A, B, ..) -> R` bound the
        // call lowers to the SAME opaque, DISJOINT `spec_fn_apply` UF the reflection
        // path uses, building the `f` receiver term IDENTICALLY (a bare `SpecFn`
        // variable path lowers to `Var { name, ty: SpecFn(..) }`) and the N-TUPLE of
        // arguments in order (`arg_type_key` makes the UF symbol per-signature, so a
        // 2-ary `Fn(u64,u64)->u64` and a unary `Fn(u64)->u64` never collide). That
        // one nameable return term is what both the caller read (`let t = f(a, b);
        // .. t ..`) and the call-site assume-ensures the extraction seam
        // (`record_closure_application_obligations`) emits resolve to. `spec_fn_apply`
        // is opaque and says NOTHING by itself; its value is pinned ONLY by that
        // seam's assume, whose ensures is exactly the independently def-side-CHECKED
        // written clause — a lying closure's def-side Counterexample poisons the whole
        // function, so a call-site assume can never rescue an unchecked ensures. For an
        // `F: Fn(..)` parameter the seam PROVES `f.requires((args,))` and assumes
        // `f.ensures((args,), result)` only under it (opaque reflection UFs); a ghost
        // `SpecFn` parameter's term stays unconstrained. The precondition is never
        // left to this lowering: an unused result is never lowered (H6), so the seam
        // proves the requires, or rejects the application, at EXTRACTION. An ARITY
        // MISMATCH is rejected there too; the error below is only a backstop for a
        // lowering reached without that seam.
        if let Some(TrustVcType::SpecFn(arg_tys, ret_ty)) = env.lookup(&name) {
            if arg_tys.len() == call.args.len() {
                let receiver = lower_syn_expr_with_depth(&call.func, env, depth)?;
                let mut lowered_args = Vec::with_capacity(call.args.len());
                for (index, (arg, arg_ty)) in call.args.iter().zip(arg_tys.iter()).enumerate() {
                    let lowered = lower_syn_expr_with_depth(arg, env, depth)?;
                    let lowered = coerce_unsuffixed_literal(lowered, arg_ty);
                    require_exact_spec_fn_value_type(
                        &lowered,
                        arg_ty,
                        &format!("SpecFn application argument {index}"),
                    )?;
                    lowered_args.push(lowered);
                }
                return Ok(crate::ir_builder::spec_fn_apply(
                    receiver,
                    arg_tys,
                    lowered_args,
                    ret_ty.as_ref().clone(),
                ));
            }
            return Err(LoweringError::UnsupportedExpr(format!(
                "direct application of closure value '{name}' with {} argument(s) does \
                 not match its {} parameter(s); this arity is deferred (reflection via \
                 `{name}.requires(..)` / `{name}.ensures(..)` is available)",
                call.args.len(),
                arg_tys.len()
            )));
        }
        let args: Vec<_> = call
            .args
            .iter()
            .map(|arg| lower_syn_expr_with_depth(arg, env, depth))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(wrapping) = lower_wrapping_free_function_call(&name, args.clone(), env) {
            return Ok(wrapping);
        }
        // Every argument is BOUND at its parameter's type, where that type
        // holds it, and the call is refused otherwise
        // (`ir_lowering::bind_call_argument`, §5b rule 6). Only an untyped
        // literal used to be retyped (and only when it fit); every other
        // argument met the callee's parameter unbound, so `inc32(255u8)` with
        // `x: i32` computed `x + 1` at 8 bits.
        let args = if let Some(param_types) = env.lookup_fn_params(&name) {
            args.into_iter()
                .enumerate()
                .map(|(index, arg)| match param_types.get(index) {
                    Some(param_ty) => crate::ir_lowering::bind_call_argument(&arg, param_ty)
                        .map_err(|arg_ty| {
                            LoweringError::TypeInference(format!(
                                "call to `{name}` passes a value of type `{}` for parameter {index} \
                                 of type `{}`, which cannot hold it",
                                arg_ty.to_type_string(),
                                param_ty.to_type_string()
                            ))
                        }),
                    None => Ok(arg),
                })
                .collect::<Result<Vec<_>, _>>()?
        } else {
            args
        };
        let args = enforce_generic_instantiation_carrier(&name, path, args, env)?;
        let return_ty = if name == "__trust_vc_dt_size" {
            TrustVcType::MathInt
        } else {
            let declared = env
                .lookup_fn(&name)
                .or_else(|| env.lookup(&name))
                .cloned()
                .ok_or_else(|| {
                    LoweringError::TypeInference(format!(
                        "unknown return type for function '{}': register it in TypeEnv via prepare_context",
                        name
                    ))
                })?;
            substitute_generic_fn_return_ty(&name, &declared, &args, path, env)?
        };
        return Ok(TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        });
    }
    Err(LoweringError::UnsupportedExpr(
        "non-path function call".into(),
    ))
}

/// NAMED refusals for the `&mut` contract vocabulary, so a spelling this engine
/// cannot give sound semantics never degrades into a silent acceptance (and
/// never into the anonymous "unknown return type for function" either).
///
/// Two groups, for two different reasons:
///
/// 1. **`final` / `mut_ref_future` / `mut_ref_current` reaching lowering at
///    all.** These are RESOLVED, with context, by the two-state resolver in
///    `vc_extraction` — ensures-only (entry ops also in `requires`), supported
///    scalar `&mut` parameters only. Reaching lowering means the resolver did
///    not claim it: a body `assert!`, a spec-function body, a function with no
///    supported `&mut` parameter. In a body position these name the endpoints
///    of a borrow the live path does not track (that is the prophecy substrate,
///    ruled DO NOT WIRE), so the only sound answer is a refusal.
///
/// 2. **`has_resolved` / `has_resolved_unsized` / `after_borrow` anywhere.**
///    `has_resolved` is a predicate over a REFERENCE (Verus axiomatizes
///    `has_resolved(t) ==> mut_ref_current(t) == mut_ref_future(t)`), and the
///    live path has no term for a reference — only for its scalar VALUE. Lowering
///    `has_resolved(a)` onto that value would identify two distinct references
///    whose values happen to coincide, so a resolution fact assumed for one would
///    transfer to the other: `#[requires(has_resolved(a))] #[ensures(has_resolved(b))]`
///    would VERIFY where Verus refutes it. `after_borrow` names a place's value
///    after a LOCAL borrow of it ends, an endpoint the live path likewise does not
///    track. Both are refused rather than approximated.
fn mut_ref_vocabulary_refusal(name: &str) -> Option<String> {
    let last = name.rsplit("::").next().unwrap_or(name);
    let two_state = match last {
        "__trust_vc_mut_ref_final" => Some("final"),
        "mut_ref_future" => Some("mut_ref_future"),
        "mut_ref_current" => Some("mut_ref_current"),
        _ => None,
    };
    if let Some(spelling) = two_state {
        return Some(format!(
            "`{spelling}()` is a `&mut` two-state contract op: it is supported in a \
             function contract clause over a supported scalar `&mut` PARAMETER \
             (`final`/`mut_ref_future` in `ensures`; `mut_ref_current`/`old` in either), \
             and is refused here. Outside that position it would name an endpoint of a \
             borrow this engine does not track, so accepting it would be a silent wrong \
             answer rather than a refusal"
        ));
    }
    match last {
        "has_resolved" | "has_resolved_unsized" => Some(
            "`has_resolved()` is refused: it is a predicate over a mutable REFERENCE, and \
             this engine models a `&mut` parameter only by the scalar VALUE behind it. \
             Lowering it onto that value would identify two distinct references whose \
             values coincide and let a resolution fact assumed for one transfer to the \
             other — a false `Verified`. Resolution tracking is not implemented"
                .to_string(),
        ),
        "after_borrow" => Some(
            "`after_borrow()` is refused: it names a place's value after a LOCAL borrow of \
             it ends, and this engine tracks borrow endpoints only for `&mut` PARAMETERS \
             (whose borrow spans the whole function). Use `final`/`mut_ref_future` on a \
             `&mut` parameter in an `ensures`"
                .to_string(),
        ),
        _ => None,
    }
}

/// Lower `__trust_vc_let_bound::<T>(value)` — the value of a body `let v: T =
/// value;` as the extractor substitutes it for `v` — as `value` BOUND at `T`
/// (`ir_lowering::int_binding`, design-trust-proof-backend.md §5b rule 6): a
/// value of type `T` as is, an untyped literal form typed at `T`, a
/// fixed-width value at `int`/`nat` lifted to the integer it denotes, and any
/// other integer value refused. `None` for any other call.
///
/// A body `let` is modelled by SUBSTITUTION, and the substituted text used to
/// carry the initializer's own type: `let v: int = x_u8; v + 1 == 256` read
/// `x + 1` in `u8`, and `let v: u8 = y_i16` was accepted (and `v` read as the
/// `i16`) where Rust and Verus reject it.
fn lower_let_bound_marker(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(segment) = path.path.segments.last() else {
        return Ok(None);
    };
    if segment.ident != crate::ir_lowering::LET_BOUND_MARKER {
        return Ok(None);
    }
    let one_type = || LoweringError::TypeInference("let-binding marker takes one type".into());
    let ty = match &segment.arguments {
        syn::PathArguments::AngleBracketed(args) if args.args.len() == 1 => match args.args.first()
        {
            Some(syn::GenericArgument::Type(ty)) => ty,
            _ => return Err(one_type()),
        },
        _ => return Err(one_type()),
    };
    let target = trust_vc_type_from_syn_type_with_env(ty, env)?;
    let (Some(value), 1) = (call.args.first(), call.args.len()) else {
        return Err(LoweringError::TypeInference(
            "let-binding marker takes one value".into(),
        ));
    };
    let value = lower_syn_expr_with_depth(value, env, depth)?;
    // An ascription the lowering cannot RESOLVE (a module-qualified alias
    // `m::MyInt`, `self::MyInt`, a generic alias `Id<int>`, a generic
    // struct `Wrap<int>` over a `Wrap<u8>`) binds only a value that holds
    // no integer, or one whose own type is spelled exactly as the
    // ascription (`let g: GOpt<u64> = GOpt::<u64>::None`): which integer
    // type it denotes is not known here, and a value substituted bare kept
    // its own (`let v: self::MyInt = x_u8; v + 1 == 0` was `Verified`).
    let spelled_alike = |value_ty: &TrustVcType| {
        let squash = |text: String| {
            text.chars()
                .filter(|c| !c.is_whitespace())
                .collect::<String>()
        };
        squash(value_ty.to_type_string()) == squash(target.to_type_string())
    };
    let value_ty = infer_expr_type(&value);
    if target.contains_opaque() && type_holds_an_integer(&value_ty) && !spelled_alike(&value_ty) {
        return Err(LoweringError::TypeInference(format!(
            "a `let` ascribed `{}`, which does not resolve to a type here, cannot bind a value \
             of type `{}`",
            quote::ToTokens::to_token_stream(ty),
            value_ty.to_type_string()
        )));
    }
    bind_at_type(value, target, "a `let`").map(Some)
}

/// `value` stored in a slot of type `target` — a `let`, an assignment, a
/// field — by rule 6's `int_binding`: a value of the slot's type as is, an
/// untyped literal form the type holds at it, a fixed-width value lifted to
/// `int`/`nat`, and a COMPOSITE only where its type agrees with the slot's at
/// every integer position (`let t: (int, int) = p`, `p: (u8, u8)`, read
/// `t.0` in `u8`, and `let v: Seq<int> = s`, `s: Seq<u8>`, read `v[0]` in
/// `u8`). Anything else is refused: unlike a call argument, a slot is never
/// WIDENED (`let v: i32 = x_i8` is a type error).
fn bind_at_type(
    value: TrustVcExpr,
    target: TrustVcType,
    slot: &str,
) -> Result<TrustVcExpr, LoweringError> {
    use crate::ir_lowering::IntBinding;
    let refuse = |found: &TrustVcType, target: &TrustVcType| {
        LoweringError::TypeInference(format!(
            "{slot} of type `{}` cannot hold a value of type `{}` (Rust and Verus reject the \
             program)",
            target.to_type_string(),
            found.to_type_string()
        ))
    };
    // A float slot holds a value of its own float type. An exact real (an
    // unsuffixed float literal, which the lowering reads as the `real` it is
    // next to a `real` peer) or an integer is refused: `let f: f64 = 300.0;`
    // held the real 300, so `f as u8` floored and wrapped (`== 44`
    // `Verified`, Rust gives 255) and `let a: f64 = 0.1; let b: f64 = 0.2;`
    // summed exactly (`a + b == 0.3` `Verified`, false in `f64`).
    if let TrustVcType::Float { .. } = target {
        let value_ty = infer_expr_type(&value);
        if matches!(value_ty, TrustVcType::Real) || crate::ir_lowering::is_integer_type(&value_ty) {
            return Err(LoweringError::TypeInference(format!(
                "{slot} of type `{}` cannot hold a value of type `{}`: an exact value is not \
                 the rounded float Rust stores",
                target.to_type_string(),
                value_ty.to_type_string()
            )));
        }
        return Ok(value);
    }
    Ok(match crate::ir_lowering::int_binding(&value, &target) {
        IntBinding::NotInteger
            if type_holds_an_integer(&target)
                && !integer_positions_agree(&infer_expr_type(&value), &target) =>
        {
            return Err(refuse(&infer_expr_type(&value), &target))
        }
        IntBinding::Same | IntBinding::NotInteger => value,
        // A slot of type `i32` holds a value of that type, not an untyped form
        // a later peer retypes: the form is pinned as a literal the source
        // types `i32` is (§5b rule 7).
        IntBinding::Literal(typed) => crate::ir_lowering::pin_untyped_at_i32(*typed),
        IntBinding::LiftToInt => TrustVcExpr::Cast {
            from_ty: infer_expr_type(&value),
            expr: Box::new(value),
            to_ty: target,
        },
        IntBinding::Mismatch(value_ty) => return Err(refuse(&value_ty, &target)),
    })
}

/// `__trust_vc_self_typed(value)` (`SELF_TYPED_MARKER`): an argument
/// substituted for a closure parameter whose type nothing here reads. Rust
/// types that parameter from EVERY call of the closure and every use in its
/// body (`let f = |a| a + 100; f(y_u8); f(200)` makes `a` a `u8`), so an
/// argument whose type only its context fixes — an untyped literal form, or
/// a name the extractor substitutes with one (`let k = 200; f(k)`) — would
/// otherwise keep its own `i32` placeholder (or exact `real`) and the body
/// would be read in the wrong type. Such a value is refused; any other value
/// carries its own type, which Rust unifies with the parameter's, and is
/// returned unchanged.
fn lower_self_typed_marker(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    if path.qself.is_some()
        || path.path.segments.len() != 1
        || path.path.segments[0].ident != crate::ir_lowering::SELF_TYPED_MARKER
    {
        return Ok(None);
    }
    let (Some(value), 1) = (call.args.first(), call.args.len()) else {
        return Err(LoweringError::TypeInference(
            "closure-argument marker takes one value".into(),
        ));
    };
    let refuse = || {
        LoweringError::UnsupportedExpr(format!(
            "`{}` is an untyped literal passed to a closure parameter whose type is not \
             written or declared: Rust types it from the closure's other calls and uses, \
             which are not read here",
            quote::ToTokens::to_token_stream(value)
        ))
    };
    if crate::ir_lowering::operators::is_unsuffixed_float_literal_tree(value) {
        return Err(refuse());
    }
    let lowered = lower_syn_expr_with_depth(value, env, depth)?;
    if crate::ir_lowering::is_untyped_literal(&lowered) {
        return Err(refuse());
    }
    Ok(Some(lowered))
}

/// `__trust_vc_bind_like(witness, value)` (`BIND_LIKE_MARKER`): `value`
/// written into a slot whose type is the type `witness` derives — the value
/// an unascribed binding held when first written, or a projection of it
/// (§5b rule 12). The value is bound there by the one slot rule
/// (`bind_at_type`, the `let` marker's): a value of the slot's type as is, a
/// literal the type holds at it, a fixed-width value under `int`/`nat`
/// lifted, a composite only at the same integer type at every integer
/// position — and anything else is refused (a slot is never widened: `v = x`
/// of an `i8` into an `i32` binding is a type error). A witness that is an
/// UNTYPED literal form (`let
/// mut i = 0`, a tuple or sequence of such literals) fixes no type: Rust
/// infers the binding's type from what it holds, so the value is its own. A
/// witness the lowering cannot type refuses the write.
fn lower_bind_like_marker(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(segment) = path.path.segments.last() else {
        return Ok(None);
    };
    if segment.ident != crate::ir_lowering::BIND_LIKE_MARKER || path.path.segments.len() != 1 {
        return Ok(None);
    }
    let (Some(witness), Some(value), 2) = (call.args.first(), call.args.get(1), call.args.len())
    else {
        return Err(LoweringError::TypeInference(
            "slot-binding marker takes a witness and a value".into(),
        ));
    };
    let witness = lower_syn_expr_with_depth(witness, env, depth)?;
    let value = lower_syn_expr_with_depth(value, env, depth)?;
    // A witness that is itself an untyped literal form fixes no type: the
    // value is its own (`let mut i = 0; i = x`), untouched by the binder.
    if crate::ir_lowering::witness_fixes_no_type(&witness) {
        return Ok(Some(value));
    }
    let slot = crate::ir_lowering::slot_type_like(&witness, &infer_expr_type(&value));
    bind_at_type(value, slot, "a write into a slot").map(Some)
}

/// Apply the expected `int` result type of a source spec function to its body.
///
/// Plain arithmetic is promoted recursively so an expression such as
/// `(x + x) + x`, with `x: u16`, is encoded as mathematical integer arithmetic
/// throughout. Explicit finite-width boundaries (`as u16`, `wrapping_add`,
/// bitwise/shift operations, and finite-returning calls) keep their own
/// semantics and are converted only after they produce a value.
///
/// "Throughout" includes arithmetic whose derived type is already `int` — an
/// operation over operands of two fixed-width types (`(x + 1) * 2i64`, `x:
/// i32`). Its operands are promoted like any other: descending only through
/// FIXED-WIDTH nodes (`TrustVcType::is_integer`) left the `i32` sum `x + 1`
/// wrapping under an `int` product, so `fn w(x: i32) -> int { (x + 1) * 2i64 }`
/// read `x + 1` in `i32` while `fn d(x: i32) -> int { x + 1 }` read it exactly.
fn promote_result_expr_to_math_int(expr: TrustVcExpr) -> Result<TrustVcExpr, LoweringError> {
    fn cast_finite(expr: TrustVcExpr, from_ty: TrustVcType) -> TrustVcExpr {
        TrustVcExpr::Cast {
            expr: Box::new(expr),
            from_ty,
            to_ty: TrustVcType::MathInt,
        }
    }

    let original_ty = infer_expr_type(&expr);
    // Integer-valued nodes whose plain arithmetic is promoted: fixed-width,
    // or already exact (`int`/`nat`, incl. a mixed-type operation).
    let integer_valued = crate::ir_lowering::is_integer_type(&original_ty);
    let promoted = match expr {
        TrustVcExpr::Arith {
            op, left, right, ..
        } if integer_valued => TrustVcExpr::Arith {
            op,
            left: Box::new(promote_result_expr_to_math_int(*left)?),
            right: Box::new(promote_result_expr_to_math_int(*right)?),
            ty: TrustVcType::MathInt,
        },
        TrustVcExpr::Neg(inner) if integer_valued => {
            TrustVcExpr::Neg(Box::new(promote_result_expr_to_math_int(*inner)?))
        }
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } if integer_valued => TrustVcExpr::Ite {
            cond,
            then_branch: Box::new(promote_result_expr_to_math_int(*then_branch)?),
            else_branch: Box::new(promote_result_expr_to_math_int(*else_branch)?),
            ty: TrustVcType::MathInt,
        },
        TrustVcExpr::Match {
            scrutinee, arms, ..
        } if integer_valued => TrustVcExpr::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|mut arm| {
                    arm.body = promote_result_expr_to_math_int(arm.body)?;
                    Ok(arm)
                })
                .collect::<Result<Vec<_>, LoweringError>>()?,
            ty: TrustVcType::MathInt,
        },
        TrustVcExpr::Let {
            name,
            ty,
            value,
            body,
        } if integer_valued => TrustVcExpr::Let {
            name,
            ty,
            // A local initializer keeps the type it inferred at the `let`;
            // only the block's result is in the function return context.
            value,
            body: Box::new(promote_result_expr_to_math_int(*body)?),
        },
        already_math
            if matches!(
                original_ty,
                TrustVcType::MathInt | TrustVcType::Nat | TrustVcType::Real
            ) =>
        {
            already_math
        }
        finite if original_ty.is_integer() => cast_finite(finite, original_ty),
        other => {
            return Err(LoweringError::TypeInference(format!(
                "source spec function body has type `{}`, expected `int`",
                infer_expr_type(&other).to_type_string()
            )))
        }
    };
    Ok(promoted)
}

/// Exposes the well-founded STRUCTURAL ordering — the existing trusted `dt_size`
/// measure UF — to the spec surface as `height(x)` and `is_smaller_than(a, b)`
/// (the value side of Verus's `decreases_to!` predicate & height intrinsic):
///
/// * `height(x)`             → `__trust_vc_dt_size(x)`, the value's structural
///   size. The datatype well-foundedness axioms give `size(x) >= 0` and
///   `size(child) < size(parent)`.
/// * `is_smaller_than(a, b)` → `dt_size(a) < dt_size(b)` for datatype arguments;
///   `0 <= a && a < b` when BOTH arguments are integer (Verus's nat-bounded
///   integer decreases order).
///
/// Both are backed by the trusted `dt_size` recurrence, so a genuine substructure
/// relation (`is_smaller_than(t, Cons(h, t))`) is PROVABLE while an unrelated pair
/// stays unprovable (fail-closed): `dt_size` of two unconstrained values is only
/// bounded `>= 0`, so `<` between them is not decidable. Only meaningful for
/// recursive datatypes — the `__trust_vc_dt_size` builtin fail-closes at encode
/// for any other argument type, so a bogus `height(5)` never verifies.
///
/// The `decreases_to!(a => b)` MACRO surface (lexicographic, `=>` syntax) is a
/// separate marker in the `trust-vc` proc-macro crate and is intentionally NOT
/// aliased here — reusing its bare name as a comma-arg call would fork the syntax.
///
/// Reserved-name guard: returns `Ok(None)` when the identifier already resolves to
/// a user function or variable, so user code defining its own `height` /
/// `is_smaller_than` keeps that meaning.
fn lower_decreases_ordering_call(
    name: &str,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    if env.lookup_fn(name).is_some() || env.lookup(name).is_some() {
        return Ok(None);
    }
    match name {
        "height" | "spec_height" => {
            if call.args.len() != 1 {
                return Ok(None);
            }
            let arg = lower_syn_expr_with_depth(&call.args[0], env, depth)?;
            Ok(Some(dt_size_measure_expr(arg)))
        }
        "is_smaller_than" => {
            if call.args.len() != 2 {
                return Ok(None);
            }
            // Lexicographic (multidecrease) form: `is_smaller_than((a1, a2, ...),
            // (b1, b2, ...))` over two tuples of EQUAL, non-empty arity. The tuple
            // is strictly smaller iff the FIRST differing component is smaller in
            // the per-component well-order, ties broken left-to-right:
            //   smaller(a1,b1) || (a1 == b1 && (smaller(a2,b2) || (a2 == b2 && ...)))
            if let (syn::Expr::Tuple(left), syn::Expr::Tuple(right)) =
                (&call.args[0], &call.args[1])
            {
                if !left.elems.is_empty() && left.elems.len() == right.elems.len() {
                    let mut components = Vec::with_capacity(left.elems.len());
                    for (le, re) in left.elems.iter().zip(right.elems.iter()) {
                        let a = lower_syn_expr_with_depth(le, env, depth)?;
                        let b = lower_syn_expr_with_depth(re, env, depth)?;
                        components.push((a, b));
                    }
                    return Ok(Some(lexicographic_smaller(components)));
                }
            }
            let smaller = lower_syn_expr_with_depth(&call.args[0], env, depth)?;
            let larger = lower_syn_expr_with_depth(&call.args[1], env, depth)?;
            Ok(Some(component_smaller(smaller, larger)))
        }
        _ => Ok(None),
    }
}

/// One component of the decreases well-order: `a` is smaller than `b`. For integer
/// components, `0 <= a && a < b` (Verus's nat-bounded order — a negative value is
/// not below, nothing is smaller than itself). For any other (datatype) component,
/// `dt_size(a) < dt_size(b)` (fail-closes at encode for non-recursive types).
pub(super) fn component_smaller(a: TrustVcExpr, b: TrustVcExpr) -> TrustVcExpr {
    if infer_expr_type(&a).is_integer() && infer_expr_type(&b).is_integer() {
        let zero = TrustVcExpr::IntLit {
            value: 0,
            ty: infer_expr_type(&a),
        };
        let nonneg = TrustVcExpr::Compare {
            op: CompareOp::Le,
            left: Box::new(zero),
            right: Box::new(a.clone()),
        };
        let strictly_less = TrustVcExpr::Compare {
            op: CompareOp::Lt,
            left: Box::new(a),
            right: Box::new(b),
        };
        return TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(nonneg),
            right: Box::new(strictly_less),
        };
    }
    TrustVcExpr::Compare {
        op: CompareOp::Lt,
        left: Box::new(dt_size_measure_expr(a)),
        right: Box::new(dt_size_measure_expr(b)),
    }
}

/// The lexicographic strict order over `[(a1,b1), (a2,b2), ...]` (non-empty):
/// `smaller(a1,b1) || (a1 == b1 && lex(rest))`. Built from the last component
/// backward. Each component uses [`component_smaller`]; ties use structural
/// equality on that component.
pub(super) fn lexicographic_smaller(components: Vec<(TrustVcExpr, TrustVcExpr)>) -> TrustVcExpr {
    let mut iter = components.into_iter().rev();
    // quality-audit: allow-expect — both callers reject empty arity before building components
    let (last_a, last_b) = iter.next().expect("non-empty tuple");
    let mut acc = component_smaller(last_a, last_b);
    for (a, b) in iter {
        let eq = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(a.clone()),
            right: Box::new(b.clone()),
        };
        let tie_break = TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(eq),
            right: Box::new(acc),
        };
        acc = TrustVcExpr::Logic {
            op: LogicOp::Or,
            left: Box::new(component_smaller(a, b)),
            right: Box::new(tie_break),
        };
    }
    acc
}

/// `__trust_vc_dt_size(arg)` — the structural-size measure of a recursive datatype
/// value (Int-valued, `>= 0` by the well-foundedness axiom). Fail-closes at encode
/// for non-recursive-datatype arguments.
fn dt_size_measure_expr(arg: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: "__trust_vc_dt_size".to_string(),
        args: vec![arg],
        return_ty: TrustVcType::MathInt,
    }
}

/// Resolve a concrete trait spec method invoked by PATH / UFCS syntax — the
/// WITH-SELF-ARG forms `<S as Tr>::f(s, ..)`, `S::f(s, ..)`, and `Tr::f(s, ..)`
/// — to the SAME `Tr__f(Box_S(s), ..)` + contract axiom that the RECEIVER
/// method-call path (`s.f()`, `dispatch/methods.rs`) produces for a concrete
/// receiver with an `impl Tr for S` (Slice 1 of #33). Previously these
/// hard-errored with "unknown return type for function 'Tr::f'".
///
/// The resolution keys on the CONCRETE TYPE of the first argument (the receiver),
/// exactly as Slice 1's registration and its method-call consumer do: the boxed
/// `MethodMeta` is registered per `(concrete_type_name, method_name)` (with the
/// trait baked into `uf_name = Tr__f`), fail-closed on any non-concrete / opaque
/// / ambiguous / never-override case. Because we reuse that already-gated
/// metadata verbatim, all of Slice 1's soundness guards carry over: the value
/// comes ONLY from the trait CONTRACT axiom (never the impl body), a
/// contract-violating impl makes the caller fail its conformance obligation, and
/// distinct impls never cross-leak.
///
/// Fail-closed envelope (returns `Ok(None)`, leaving the existing
/// unknown-return-type error, for anything not cleanly resolvable):
/// * a bare single-segment, non-qself path (`f(x)`) — an ordinary free-function
///   call, never a trait-method UFCS;
/// * a path whose full name IS a registered free function or variable — those
///   keep their existing resolution byte-for-byte (this branch only ever adds
///   resolution to paths that currently ERROR);
/// * no receiver argument (`<bool as Tr>::f()` — the no-self associated-function
///   case is explicitly out of scope, there is no receiver to box);
/// * a first-argument type with no Slice-1 concrete-impl `MethodMeta` for the
///   named method, or one whose `box_receiver` is `None` (the generic/accessor
///   path, which carries no UFCS meaning here).
fn lower_concrete_trait_path_call(
    name: &str,
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    // Only a trait-qualified / type-qualified / qself path can name a trait
    // method by UFCS; a bare `f(x)` never can.
    if path.path.segments.len() < 2 && path.qself.is_none() {
        return Ok(None);
    }
    // Never shadow an already-registered free function or variable: those keep
    // their existing resolution (the generic call path below). This confines the
    // new behavior to paths that would otherwise hit the unknown-return-type
    // error, so it is purely additive.
    if env.lookup_fn(name).is_some() || env.lookup(name).is_some() {
        return Ok(None);
    }
    // The method is the last path segment; the receiver is the first argument.
    let Some(method_segment) = path.path.segments.last() else {
        return Ok(None);
    };
    let method_name = method_segment.ident.to_string();
    let Some(receiver_arg) = call.args.first() else {
        return Ok(None);
    };

    // Lower the receiver and derive its concrete type name — the exact key Slice
    // 1 registers under (the struct's bare `to_type_string()`), matching how the
    // method-call path computes `type_name` from the receiver.
    let receiver = lower_syn_expr_with_depth(receiver_arg, env, depth)?;
    let type_name = infer_expr_type(&receiver).to_type_string();

    // Resolve ONLY through a Slice-1 concrete-impl `MethodMeta` that carries a
    // box bridge. A missing entry or a `None` box_receiver falls through to the
    // existing error (fail closed).
    let Some(meta) = env.lookup_method(&type_name, &method_name) else {
        return Ok(None);
    };
    let Some(box_fn) = meta.box_receiver.clone() else {
        return Ok(None);
    };
    let uf_name = meta.uf_name.clone();
    let return_ty = meta.return_type.clone();
    let param_types = meta.param_types.clone();

    // Build `Tr__f(Box_S(receiver), ..rest)` — byte-identical to the receiver
    // method-call path (`dispatch/methods.rs`): the concrete receiver is lifted
    // into the trait UF's `Poly` self-domain via the impl's `Box_S` bridge, and
    // the value is supplied by the trait's declared postcondition axiom.
    let boxed_receiver = TrustVcExpr::FnCall {
        name: box_fn,
        args: vec![receiver],
        return_ty: TrustVcType::Poly,
    };
    let mut args = vec![boxed_receiver];
    for (index, arg) in call.args.iter().skip(1).enumerate() {
        let lowered = lower_syn_expr_with_depth(arg, env, depth)?;
        if let Some(param_ty) = param_types.get(index) {
            // Bound at the parameter's type, as every call argument is
            // (`ir_lowering::bind_call_argument`).
            let bound =
                crate::ir_lowering::bind_call_argument(&lowered, param_ty).map_err(|arg_ty| {
                    LoweringError::TypeInference(format!(
                        "call to `{method_name}` passes a value of type `{}` for parameter \
                         {index} of type `{}`, which cannot hold it",
                        arg_ty.to_type_string(),
                        param_ty.to_type_string()
                    ))
                })?;
            args.push(bound);
        } else {
            args.push(lowered);
        }
    }
    Ok(Some(TrustVcExpr::FnCall {
        name: uf_name,
        args,
        return_ty,
    }))
}

/// Lower the free-fn surface of Phase C closure reflection —
/// `call_requires(f, (a, ..))` / `call_ensures(f, (a, ..), r)` — to the same
/// opaque `call_requires%` / `call_ensures%` UF predicates as the `f.requires(..)`
/// / `f.ensures(..)` method form. Returns `Ok(None)` for any other call so the
/// generic path is unaffected; fails closed when the first argument is not a
/// known `SpecFn`-typed value or the args tuple mismatches.
fn lower_closure_reflection_free_fn(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let is_requires = path_matches_suffix(&path.path, &["call_requires"]);
    let is_ensures = path_matches_suffix(&path.path, &["call_ensures"]);
    if !is_requires && !is_ensures {
        return Ok(None);
    }

    let expected = if is_ensures { 3 } else { 2 };
    if call.args.len() != expected {
        return Err(LoweringError::UnsupportedExpr(format!(
            "{} expects {expected} argument(s) (the closure, an args tuple{}), got {}",
            if is_ensures {
                "call_ensures"
            } else {
                "call_requires"
            },
            if is_ensures { ", and a result" } else { "" },
            call.args.len()
        )));
    }

    let function = lower_syn_expr_with_depth(&call.args[0], env, depth)?;
    let TrustVcType::SpecFn(arg_tys, ret_ty) = infer_expr_type(&function) else {
        return Err(LoweringError::UnsupportedExpr(
            "closure reflection requires a known SpecFn closure value as its first argument".into(),
        ));
    };

    let syn::Expr::Tuple(tuple) = unparen_call_arg(&call.args[1]) else {
        return Err(LoweringError::UnsupportedExpr(
            "closure reflection expects its arguments as a tuple, e.g. `call_requires(f, (a,))`"
                .into(),
        ));
    };
    if tuple.elems.len() != arg_tys.len() {
        return Err(LoweringError::UnsupportedExpr(format!(
            "closure reflection argument-tuple arity {} does not match the closure's {} parameter(s)",
            tuple.elems.len(),
            arg_tys.len()
        )));
    }
    let mut lowered_args = Vec::with_capacity(arg_tys.len());
    for (index, (elem, ty)) in tuple.elems.iter().zip(arg_tys.iter()).enumerate() {
        let lowered = lower_syn_expr_with_depth(elem, env, depth)?;
        let lowered = coerce_unsuffixed_literal(lowered, ty);
        require_exact_spec_fn_value_type(
            &lowered,
            ty,
            &format!("closure reflection argument {index}"),
        )?;
        lowered_args.push(lowered);
    }

    if is_ensures {
        let result = lower_syn_expr_with_depth(&call.args[2], env, depth)?;
        let result = coerce_unsuffixed_literal(result, &ret_ty);
        require_exact_spec_fn_value_type(&result, &ret_ty, "closure reflection result")?;
        Ok(Some(crate::ir_builder::call_ensures(
            function,
            &arg_tys,
            lowered_args,
            result,
            &ret_ty,
        )))
    } else {
        Ok(Some(crate::ir_builder::call_requires(
            function,
            &arg_tys,
            lowered_args,
        )))
    }
}

fn unparen_call_arg(expr: &syn::Expr) -> &syn::Expr {
    let mut current = expr;
    while let syn::Expr::Paren(paren) = current {
        current = &paren.expr;
    }
    current
}

/// Monomorphize a generic function call's DECLARED return type when it mentions
/// a `TypeParam`.
///
/// For a generic spec/exec fn whose declared return type contains a `TypeParam`
/// (e.g. `fn generic_id<A>(value: A) -> A`), a call site like
/// `generic_id::<Pair<u64, u8>>(value)` should produce a value of the concrete
/// carrier type `Pair<u64, u8>` so that a following field projection
/// (`projected.a`) resolves, instead of failing closed with
/// `field 'a' on type 'A'`. We bind the callee's `TypeParam`s from (1) the
/// lowered argument types against the declared parameter types and (2) the
/// explicit turbofish type arguments, then substitute the declared return.
///
/// The encoder bridges the type-erased `Poly` call result back to this concrete
/// carrier through `Unbox_T`, keyed on the DECLARED return being a `TypeParam`
/// (so both the unsubstituted-`TypeParam` return and this monomorphized concrete
/// carrier go through the same bridge). When the declared return mentions no
/// `TypeParam`, this is the identity. Part of #2778.
fn substitute_generic_fn_return_ty(
    name: &str,
    declared_return: &TrustVcType,
    lowered_args: &[TrustVcExpr],
    path: &syn::ExprPath,
    env: &TypeEnv,
) -> Result<TrustVcType, LoweringError> {
    let mut declared_params = Vec::new();
    collect_type_params(declared_return, &mut declared_params);
    if declared_params.is_empty() {
        return Ok(declared_return.clone());
    }

    let mut bindings: Vec<(String, TrustVcType)> = Vec::new();
    // (1) Bind from the lowered argument types against the declared parameter
    //     types. For `generic_id<A>(value: A)` called with a `Pair<u64, u8>`
    //     argument this binds `A -> Pair<u64, u8>`.
    if let Some(param_types) = env.lookup_fn_params(name) {
        for (param_ty, arg) in param_types.iter().zip(lowered_args) {
            infer_type_param_bindings(param_ty, &infer_expr_type(arg), &mut bindings);
        }
    }

    // (2) Supplement from the turbofish explicit type argument. The callee's
    //     type-parameter declaration order is not tracked in the lowering env,
    //     so we only consume the turbofish for the identity / single-type-param
    //     shape: a declared return that is itself a bare `TypeParam` still left
    //     unbound by the argument pass, with exactly one explicit type arg. This
    //     never overrides a binding inferred from the arguments.
    if let TrustVcType::TypeParam(ret_param) = declared_return {
        if !bindings.iter().any(|(param, _)| param == ret_param) {
            if let Some(explicit) = sole_turbofish_type_arg(path, env)? {
                bindings.push((ret_param.clone(), explicit));
            }
        }
    }

    Ok(substitute_type_params(declared_return, &bindings))
}

/// H10, call-site half: the argument at a CARRYING position must be the
/// instantiation the turbofish names.
///
/// A generic source function call lowers to `name(args)`; the encoder keeps
/// instantiations apart only through the type-keyed `Box_P` it wraps around the
/// argument at a parameter registered as exactly `TypeParam(P)`, keyed on that
/// argument's LOWERED type. Declaration-time registration refuses generics no
/// position carries (`spec_function_catalog::check_generic_declaration`), so
/// here only the carrier's faithfulness is left to check:
///
/// * no turbofish, or no `TypeParam` position: nothing to check — the argument's
///   own type is Rust's inference (the `i32` literal default included), and a
///   declaration with no carrying position survives registration only when its
///   value is instantiation-uniform or datatype-monomorphized;
/// * a turbofish over a declaration whose carriage-checked registration
///   recorded its generic parameter ORDER: each explicit argument `G` is mapped
///   onto its declared parameter `P`, and at every position carrying `P` an
///   unsuffixed literal is coerced to `G` (`bare::<u8>(0)` used to box both
///   `bare::<u8>(0)` and `bare::<u16>(0)` as `Box_i32(0)`) and an argument of any
///   other lowered type fails closed; `_` defers to inference. An argument
///   count that differs from the declaration fails closed;
/// * no recorded order: one explicit type argument over one carried parameter
///   is checked the same way; anything else (two or more explicit arguments,
///   more than one carried parameter, a const argument) cannot be mapped onto
///   positions and fails closed.
fn enforce_generic_instantiation_carrier(
    name: &str,
    path: &syn::ExprPath,
    mut args: Vec<TrustVcExpr>,
    env: &TypeEnv,
) -> Result<Vec<TrustVcExpr>, LoweringError> {
    let Some(syn::PathArguments::AngleBracketed(generic_args)) =
        path.path.segments.last().map(|segment| &segment.arguments)
    else {
        return Ok(args);
    };
    let explicit = generic_args
        .args
        .iter()
        .filter(|arg| {
            matches!(
                arg,
                syn::GenericArgument::Type(_) | syn::GenericArgument::Const(_)
            )
        })
        .collect::<Vec<_>>();
    if explicit.is_empty() {
        return Ok(args);
    }
    let Some(param_types) = env.lookup_fn_params(name) else {
        return Ok(args);
    };
    let mut carried: Vec<&str> = Vec::new();
    for param_ty in param_types {
        if let TrustVcType::TypeParam(param) = param_ty {
            if !carried.contains(&param.as_str()) {
                carried.push(param.as_str());
            }
        }
    }
    if carried.is_empty() {
        return Ok(args);
    }
    let refuse = |why: String| {
        LoweringError::UnsupportedExpr(format!(
            "generic instantiation not carried: call `{name}` {why}; TrustVc fails closed \
             instead of guessing which solver term carries the instantiation"
        ))
    };

    // Pair each explicit argument with the declared parameter it instantiates.
    let pairs: Vec<(String, &syn::GenericArgument)> =
        if let Some(declared) = env.lookup_fn_generic_params(name) {
            if declared.len() != explicit.len() {
                return Err(refuse(format!(
                    "supplies {} explicit generic argument(s) to a declaration with {} type/const \
                     generic parameter(s)",
                    explicit.len(),
                    declared.len()
                )));
            }
            declared
                .iter()
                .cloned()
                .zip(explicit.iter().copied())
                .collect()
        } else if let ([arg], [carried_param]) = (explicit.as_slice(), carried.as_slice()) {
            vec![((*carried_param).to_string(), *arg)]
        } else {
            return Err(refuse(format!(
                "supplies {} explicit generic argument(s) over {} carried type parameter(s), and \
                 its registration recorded no generic declaration order, so the turbofish \
                 cannot be mapped onto the carrying positions",
                explicit.len(),
                carried.len()
            )));
        };

    for (param, arg) in pairs {
        let carried_ty = TrustVcType::TypeParam(param.clone());
        if !param_types.contains(&carried_ty) {
            // Not a carrying position: the declaration gate already decided
            // whether this parameter may stay uncarried.
            continue;
        }
        let instantiation = match arg {
            syn::GenericArgument::Type(syn::Type::Infer(_)) => continue,
            syn::GenericArgument::Type(ty) => env.resolve_syn_type(ty)?,
            _ => {
                return Err(refuse(format!(
                    "supplies a const generic argument for the carried type parameter `{param}`"
                )))
            }
        };
        for (index, param_ty) in param_types.iter().enumerate() {
            if *param_ty != carried_ty {
                continue;
            }
            let Some(arg) = args.get_mut(index) else {
                continue;
            };
            let lowered = std::mem::replace(arg, TrustVcExpr::BoolLit(false));
            // An untyped literal form (a lone literal, or the value of a
            // binding whose type is not determined elsewhere) takes the
            // instantiation it is passed at, literal by literal.
            let coerced =
                match crate::ir_lowering::untyped_literal_at_peer(&lowered, &instantiation) {
                    Some(typed) => typed,
                    None => coerce_unsuffixed_literal(lowered, &instantiation),
                };
            let actual = infer_expr_type(&coerced);
            if actual.to_type_string() != instantiation.to_type_string() {
                return Err(refuse(format!(
                    "passes an argument of type `{}` at the position carrying `{param}` = `{}`",
                    actual.to_type_string(),
                    instantiation.to_type_string()
                )));
            }
            *arg = coerced;
        }
    }
    Ok(args)
}

/// Resolve the sole explicit turbofish type argument on a function-call path
/// (e.g. the `Pair<u64, u8>` in `generic_id::<Pair<u64, u8>>(..)`), if exactly
/// one is present. Returns `None` when the path carries no angle-bracketed type
/// arguments or more than one (the latter is left to argument-based binding so
/// we never guess a declaration-order mapping).
fn sole_turbofish_type_arg(
    path: &syn::ExprPath,
    env: &TypeEnv,
) -> Result<Option<TrustVcType>, LoweringError> {
    // A function's own generic arguments live on the LAST segment; a turbofish
    // on an earlier segment (`Type::<X>::f`) names the owning type instead.
    let Some(syn::PathArguments::AngleBracketed(args)) =
        path.path.segments.last().map(|segment| &segment.arguments)
    else {
        return Ok(None);
    };
    let mut type_args = args.args.iter().filter_map(|arg| match arg {
        syn::GenericArgument::Type(ty) => Some(ty),
        _ => None,
    });
    let Some(first) = type_args.next() else {
        return Ok(None);
    };
    if type_args.next().is_some() {
        return Ok(None);
    }
    env.resolve_syn_type(first).map(Some)
}

fn explicit_constructor_type_arg_bindings(
    path: &syn::ExprPath,
    meta: &crate::ir_lowering::env::DatatypeVariantMeta,
    env: &TypeEnv,
) -> Result<Vec<(String, TrustVcType)>, LoweringError> {
    // The explicit type arguments live on the path segment that names the
    // *datatype*. For an enum variant constructor `Type::<Args>::Variant` that
    // is the second-to-last segment; for a tuple/unit *struct* constructor the
    // type itself is the constructor (`Type::<Args>`), so the turbofish lives on
    // the last segment. Scan for whichever segment carries angle-bracketed
    // arguments rather than assuming the second-to-last position: a generic
    // tuple struct (`TupleThing::<bool, bool>(..)`) is a single-segment path, so
    // the old `rev().nth(1)` lookup found nothing, left the fields at their
    // generic `TypeParam` sort (`Poly`), and the constructor apply then mismatched
    // the concrete `Bool` argument sorts ("sort mismatch in apply: got Bool").
    let Some(args) = path
        .path
        .segments
        .iter()
        .find_map(|segment| match &segment.arguments {
            syn::PathArguments::AngleBracketed(args) => Some(args),
            _ => None,
        })
    else {
        return Ok(Vec::new());
    };
    let explicit_args = args
        .args
        .iter()
        .filter_map(|arg| match arg {
            syn::GenericArgument::Type(ty) => Some(env.resolve_syn_type(ty)),
            _ => None,
        })
        .collect::<Result<Vec<_>, _>>()?;
    if explicit_args.is_empty() {
        return Ok(Vec::new());
    }
    let mut params = Vec::new();
    collect_type_params(&meta.return_ty, &mut params);
    for (_, field_ty) in &meta.fields {
        collect_type_params(field_ty, &mut params);
    }
    params.dedup();
    // An enum-variant constructor written `Enum::<Args>::Variant` (e.g.
    // `Choice::<u64>::First(..)`) attaches `<Args>` to the ENUM `Choice`, NOT to
    // the variant `First` (which declares 0 type params of its own). When the
    // resolved carrier is ALREADY CONCRETE — no remaining `TypeParam`s, because a
    // use/match site has monomorphized it to `Choice<u64>` (concrete field sorts,
    // `params` empty) — the enum-level turbofish is redundant: it merely restates
    // the instantiation the carrier already reflects, and there is nothing left to
    // bind. The downstream `FnCall` then uses `meta.uf_name` / `meta.return_ty`
    // verbatim (the concrete `Choice<u64>` constructor + carrier the match arms
    // select on). Returning no bindings here is the same outcome as the
    // turbofish-free constructor path, so it is completeness-restoring and
    // soundness-neutral (a wrong-typed argument still mismatches the concrete
    // field sort downstream, and a disagreeing carrier resolves ambiguously).
    //
    // Without this guard the enum-level turbofish was mis-attributed as a VARIANT
    // type-arg and checked against the concrete carrier's 0 params, firing
    // "constructor 'Choice::First' expects 0 type argument(s), got 1". The
    // generic TEMPLATE-carrier path below (`params` non-empty, e.g. the
    // `TupleThing<A, B>` tuple struct) is unchanged and still binds + arity-checks
    // each `<Args>` against the carrier's own type params.
    if params.is_empty() {
        return Ok(Vec::new());
    }
    if params.len() != explicit_args.len() {
        return Err(LoweringError::TypeInference(format!(
            "constructor '{}::{}' expects {} type argument(s), got {}",
            datatype_base_name(&meta.datatype_name),
            meta.variant_name,
            params.len(),
            explicit_args.len()
        )));
    }
    Ok(params.into_iter().zip(explicit_args).collect())
}

fn collect_type_params(ty: &TrustVcType, params: &mut Vec<String>) {
    match ty {
        TrustVcType::TypeParam(name) if !params.contains(name) => params.push(name.clone()),
        TrustVcType::Seq(inner)
        | TrustVcType::Array(inner, _)
        | TrustVcType::Set(inner)
        | TrustVcType::Multiset(inner) => collect_type_params(inner, params),
        TrustVcType::Map(key, value) => {
            collect_type_params(key, params);
            collect_type_params(value, params);
        }
        TrustVcType::SpecFn(args, ret) => {
            for arg in args {
                collect_type_params(arg, params);
            }
            collect_type_params(ret, params);
        }
        TrustVcType::Datatype { variants, .. } => {
            for variant in variants {
                for (_, field_ty) in &variant.fields {
                    collect_type_params(field_ty, params);
                }
            }
        }
        _ => {}
    }
}

/// Whether `ty` is a datatype carrier that references itself recursively
/// (a `RecursiveRef` back to its own carrier name, possibly modulo the
/// generic-argument suffix). Used to gate argument-driven monomorphization to
/// the recursive-datatype case.
fn carrier_is_self_recursive(ty: &TrustVcType) -> bool {
    let TrustVcType::Datatype { name, variants } = ty else {
        return false;
    };
    let base = datatype_base_name(name);
    variants.iter().any(|variant| {
        variant.fields.iter().any(|(_, field_ty)| {
            matches!(field_ty, TrustVcType::RecursiveRef(target)
                if target == name || datatype_base_name(target) == base)
        })
    })
}

/// Monomorphizes a constructor's declared carrier return type under `bindings`.
///
/// Delegates to [`TrustVcType::monomorphize`], which substitutes `TypeParam`s
/// and — for a datatype carrier with non-empty bindings — renames the carrier
/// and its self-`RecursiveRef` edges to the per-instantiation name
/// (`GList` -> `GList<i32>`, `tail: RecursiveRef("GList")` ->
/// `RecursiveRef("GList<i32>")`). With empty bindings it is the identity, so a
/// concrete builtin carrier such as `List<i32>` is preserved verbatim (it must
/// NOT be stripped to a bare `List`, which would split one carrier into two and
/// trip the false mutual-recursion guard).
fn substitute_constructor_return_ty(
    return_ty: &TrustVcType,
    bindings: &[(String, TrustVcType)],
) -> TrustVcType {
    return_ty.monomorphize(bindings)
}

fn lower_core_mem_size_of_call(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(ty) = core_mem_layout_intrinsic_type_arg("size_of", path, call)? else {
        return Ok(None);
    };
    let value = known_layout_size_bytes(ty, env)?;
    Ok(Some(TrustVcExpr::IntLit {
        value: value as i128,
        ty: TrustVcType::Uint {
            width: crate::ir::pointer_width(),
        },
    }))
}

fn lower_core_mem_align_of_call(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(ty) = core_mem_layout_intrinsic_type_arg("align_of", path, call)? else {
        return Ok(None);
    };
    let value = known_layout_align_bytes(ty, env)?;
    Ok(Some(TrustVcExpr::IntLit {
        value: value as i128,
        ty: TrustVcType::Uint {
            width: crate::ir::pointer_width(),
        },
    }))
}

fn core_mem_layout_intrinsic_type_arg<'a>(
    intrinsic: &str,
    path: &'a syn::ExprPath,
    call: &'a syn::ExprCall,
) -> Result<Option<&'a syn::Type>, LoweringError> {
    if !(path_matches_suffix(&path.path, &["core", "mem", intrinsic])
        || path_matches_suffix(&path.path, &["std", "mem", intrinsic])
        || path_matches_suffix(&path.path, &["mem", intrinsic]))
    {
        return Ok(None);
    }
    let qualified_name = format!("core::mem::{intrinsic}");
    if !call.args.is_empty() {
        return Err(LoweringError::UnsupportedExpr(format!(
            "{qualified_name} expects 0 args, got {}",
            call.args.len()
        )));
    }
    let Some(segment) = path.path.segments.last() else {
        return Ok(None);
    };
    let syn::PathArguments::AngleBracketed(args) = &segment.arguments else {
        return Err(LoweringError::UnsupportedExpr(format!(
            "{qualified_name} requires an explicit type argument"
        )));
    };
    let mut type_args = args.args.iter().filter_map(|arg| match arg {
        syn::GenericArgument::Type(ty) => Some(ty),
        _ => None,
    });
    let Some(ty) = type_args.next() else {
        return Err(LoweringError::UnsupportedExpr(format!(
            "{qualified_name} requires an explicit type argument"
        )));
    };
    if type_args.next().is_some() {
        return Err(LoweringError::TypeInference(format!(
            "{qualified_name} expects exactly one type argument"
        )));
    }
    Ok(Some(ty))
}

fn known_layout_size_bytes(ty: &syn::Type, env: &TypeEnv) -> Result<usize, LoweringError> {
    match ty {
        syn::Type::Reference(_) | syn::Type::Ptr(_) => Ok(pointer_size_bytes()),
        syn::Type::Array(array) => {
            let elem_size = known_layout_size_bytes(&array.elem, env)?;
            let len = array_len_literal(&array.len)?;
            elem_size.checked_mul(len).ok_or_else(|| {
                LoweringError::TypeInference("core::mem::size_of array size overflows".into())
            })
        }
        _ => {
            let resolved = env.resolve_syn_type(ty)?;
            known_layout_size_bytes_for_trust_vc_type(&resolved)
        }
    }
}

fn known_layout_align_bytes(ty: &syn::Type, env: &TypeEnv) -> Result<usize, LoweringError> {
    match ty {
        syn::Type::Reference(_) | syn::Type::Ptr(_) => Ok(pointer_align_bytes()),
        syn::Type::Array(array) => known_layout_align_bytes(&array.elem, env),
        _ => {
            if let Some(value) = direct_primitive_align_bytes(ty) {
                return Ok(value);
            }
            let resolved = env.resolve_syn_type(ty)?;
            known_layout_align_bytes_for_trust_vc_type(&resolved)
        }
    }
}

fn known_layout_size_bytes_for_trust_vc_type(ty: &TrustVcType) -> Result<usize, LoweringError> {
    match ty {
        TrustVcType::Unit => Ok(0),
        TrustVcType::Bool => Ok(1),
        TrustVcType::Int { width } | TrustVcType::Uint { width } | TrustVcType::Float { width } => {
            Ok((*width / 8) as usize)
        }
        TrustVcType::Char => Ok(4),
        TrustVcType::Array(elem, len) => known_layout_size_bytes_for_trust_vc_type(elem)?
            .checked_mul(*len)
            .ok_or_else(|| {
                LoweringError::TypeInference("core::mem::size_of array size overflows".into())
            }),
        _ => Err(LoweringError::UnsupportedExpr(format!(
            "core::mem::size_of is only modeled for primitive, pointer/reference, and fixed-array types; got '{}'",
            ty.to_type_string()
        ))),
    }
}

fn known_layout_align_bytes_for_trust_vc_type(ty: &TrustVcType) -> Result<usize, LoweringError> {
    match ty {
        TrustVcType::Unit => Ok(std::mem::align_of::<()>()),
        TrustVcType::Bool => Ok(std::mem::align_of::<bool>()),
        TrustVcType::Int { width } | TrustVcType::Uint { width } => {
            integer_align_bytes(*width).ok_or_else(|| unsupported_align_of_type(ty))
        }
        TrustVcType::Float { width } => {
            float_align_bytes(*width).ok_or_else(|| unsupported_align_of_type(ty))
        }
        TrustVcType::Char => Ok(std::mem::align_of::<char>()),
        TrustVcType::Array(elem, _) => known_layout_align_bytes_for_trust_vc_type(elem),
        _ => Err(unsupported_align_of_type(ty)),
    }
}

fn direct_primitive_align_bytes(ty: &syn::Type) -> Option<usize> {
    let syn::Type::Path(type_path) = ty else {
        return None;
    };
    if type_path.qself.is_some() || type_path.path.segments.len() != 1 {
        return None;
    }
    let segment = &type_path.path.segments[0];
    if !matches!(segment.arguments, syn::PathArguments::None) {
        return None;
    }
    match segment.ident.to_string().as_str() {
        "()" => Some(std::mem::align_of::<()>()),
        "bool" => Some(std::mem::align_of::<bool>()),
        "char" => Some(std::mem::align_of::<char>()),
        "i8" => Some(std::mem::align_of::<i8>()),
        "u8" => Some(std::mem::align_of::<u8>()),
        "i16" => Some(std::mem::align_of::<i16>()),
        "u16" => Some(std::mem::align_of::<u16>()),
        "i32" => Some(std::mem::align_of::<i32>()),
        "u32" => Some(std::mem::align_of::<u32>()),
        "i64" => Some(std::mem::align_of::<i64>()),
        "u64" => Some(std::mem::align_of::<u64>()),
        "i128" => Some(std::mem::align_of::<i128>()),
        "u128" => Some(std::mem::align_of::<u128>()),
        "isize" => Some(std::mem::align_of::<isize>()),
        "usize" => Some(std::mem::align_of::<usize>()),
        "f32" => Some(std::mem::align_of::<f32>()),
        "f64" => Some(std::mem::align_of::<f64>()),
        _ => None,
    }
}

fn integer_align_bytes(width: u32) -> Option<usize> {
    match width {
        8 => Some(std::mem::align_of::<u8>()),
        16 => Some(std::mem::align_of::<u16>()),
        32 => Some(std::mem::align_of::<u32>()),
        64 => Some(std::mem::align_of::<u64>()),
        128 => Some(std::mem::align_of::<u128>()),
        _ => None,
    }
}

fn float_align_bytes(width: u32) -> Option<usize> {
    match width {
        32 => Some(std::mem::align_of::<f32>()),
        64 => Some(std::mem::align_of::<f64>()),
        _ => None,
    }
}

fn unsupported_align_of_type(ty: &TrustVcType) -> LoweringError {
    LoweringError::UnsupportedExpr(format!(
        "core::mem::align_of is only modeled for primitive, pointer/reference, and fixed-array types; got '{}'",
        ty.to_type_string()
    ))
}

fn array_len_literal(expr: &syn::Expr) -> Result<usize, LoweringError> {
    let syn::Expr::Lit(lit) = expr else {
        return Err(LoweringError::UnsupportedExpr(
            "core::mem::size_of only supports arrays with literal lengths".into(),
        ));
    };
    let syn::Lit::Int(int_lit) = &lit.lit else {
        return Err(LoweringError::UnsupportedExpr(
            "core::mem::size_of only supports arrays with integer literal lengths".into(),
        ));
    };
    int_lit.base10_parse::<usize>().map_err(|err| {
        LoweringError::TypeInference(format!(
            "core::mem::size_of array length is not a valid usize: {err}"
        ))
    })
}

fn pointer_size_bytes() -> usize {
    (crate::ir::pointer_width() / 8) as usize
}

fn pointer_align_bytes() -> usize {
    std::mem::align_of::<*const ()>()
}

fn lower_seq_from_fn_call(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(method_segment) = path.path.segments.last() else {
        return Ok(None);
    };
    let method_name = method_segment.ident.to_string();
    if !matches!(method_name.as_str(), "from_fn" | "new") {
        return Ok(None);
    }

    let Some(seq_segment) = path.path.segments.iter().rev().nth(1) else {
        return Ok(None);
    };
    if seq_segment.ident != "Seq" && !expr_path_to_string(path).ends_with("Seq::new") {
        return Ok(None);
    }
    if method_name == "new" && call.args.is_empty() {
        return Ok(None);
    }

    if call.args.len() != 2 {
        return Err(LoweringError::UnsupportedExpr(format!(
            "Seq::{method_name} expects 2 args, got {}",
            call.args.len()
        )));
    }

    let usize_ty = TrustVcType::Uint {
        width: crate::ir::pointer_width(),
    };
    let len_arg = call.args.first().ok_or_else(|| {
        LoweringError::UnsupportedExpr(format!(
            "Seq::{method_name} expects 2 args, got {}",
            call.args.len()
        ))
    })?;
    let len = lower_syn_expr_with_depth(len_arg, env, depth)?;
    let len = coerce_unsuffixed_literal(len, &usize_ty);
    let len_ty = infer_expr_type(&len);
    if len_ty != usize_ty {
        return Err(LoweringError::TypeInference(format!(
            "Seq::{method_name} length argument must be usize, got '{}'",
            len_ty.to_type_string()
        )));
    }

    let spec_arg = call.args.iter().nth(1).ok_or_else(|| {
        LoweringError::UnsupportedExpr(format!(
            "Seq::{method_name} expects 2 args, got {}",
            call.args.len()
        ))
    })?;
    // Normalize a bare closure into an implicit `SpecFn::new(...)`. The element
    // index parameter is always `usize`, so an untyped binder (`|i| ...`) infers
    // `usize`; the param-type check below still fails closed on any mismatch.
    let seq_expected_params = [usize_ty.clone()];
    let mut spec_fn = lower_spec_fn_arg(spec_arg, env, depth, Some(&seq_expected_params[..]))?;
    let TrustVcExpr::SpecClosure { params, ty, .. } = &spec_fn else {
        return Err(LoweringError::UnsupportedExpr(format!(
            "Seq::{method_name} expects SpecFn::new(...) as its second argument"
        )));
    };
    let [(_, param_ty)] = params.as_slice() else {
        return Err(LoweringError::TypeInference(format!(
            "Seq::{method_name} requires a unary SpecFn<usize, T>, got {} parameter(s)",
            params.len()
        )));
    };
    if param_ty != &usize_ty {
        return Err(LoweringError::TypeInference(format!(
            "Seq::{method_name} requires SpecFn<usize, T>, got SpecFn<{}, _>",
            param_ty.to_type_string()
        )));
    }
    let TrustVcType::SpecFn(_, ret_ty) = ty else {
        return Err(LoweringError::TypeInference(format!(
            "Seq::{method_name} second argument did not lower to a SpecFn"
        )));
    };

    let mut closure_ret_ty = ret_ty.as_ref().clone();
    let elem_ty = match explicit_seq_elem_type(seq_segment, env)? {
        Some(explicit_ty) if explicit_ty == closure_ret_ty => explicit_ty,
        Some(explicit_ty) => {
            coerce_seq_from_fn_closure_body(&mut spec_fn, &explicit_ty)?;
            let TrustVcExpr::SpecClosure {
                ty: TrustVcType::SpecFn(_, ret_ty),
                ..
            } = &spec_fn
            else {
                unreachable!("validated SpecClosure above");
            };
            closure_ret_ty = ret_ty.as_ref().clone();
            if explicit_ty != closure_ret_ty {
                return Err(LoweringError::TypeInference(format!(
                    "Seq::{method_name} closure returns '{}', but explicit Seq element type is '{}'",
                    closure_ret_ty.to_type_string(),
                    explicit_ty.to_type_string()
                )));
            }
            explicit_ty
        }
        None => closure_ret_ty,
    };

    Ok(Some(TrustVcExpr::FnCall {
        name: crate::ir_lowering::SEQ_FROM_FN_BUILTIN.to_string(),
        args: vec![len, spec_fn],
        return_ty: TrustVcType::Seq(Box::new(elem_ty)),
    }))
}

fn coerce_seq_from_fn_closure_body(
    spec_fn: &mut TrustVcExpr,
    elem_ty: &TrustVcType,
) -> Result<(), LoweringError> {
    let TrustVcExpr::SpecClosure { body, ty, .. } = spec_fn else {
        return Ok(());
    };
    let TrustVcType::SpecFn(_, ret_ty) = ty else {
        return Ok(());
    };
    let coerced_body = coerce_unsuffixed_literal((**body).clone(), elem_ty);
    if infer_expr_type(&coerced_body) == elem_ty.clone() {
        **body = coerced_body;
        **ret_ty = elem_ty.clone();
    }
    Ok(())
}

/// Lower `Set::new(|x: T| pred)` — the set-comprehension constructor — to the
/// `SET_NEW_BUILTIN` builtin call.
///
/// Mirrors `lower_seq_from_fn_call`: the element type is taken from the unary
/// closure parameter (or an explicit `Set::<T>::new` type argument, when both
/// agree), and the closure must return `bool`. The encoder turns this into a
/// fresh set `s` constrained by `forall x. s.contains(x) <=> pred(x)`.
fn lower_set_new_call(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(method_segment) = path.path.segments.last() else {
        return Ok(None);
    };
    if method_segment.ident != "new" {
        return Ok(None);
    }
    // Require the receiver path segment to be `Set` (e.g. `Set::new`,
    // `Set::<int>::new`, `vstd::set::Set::new`). This disambiguates from
    // `Seq::new`/`SpecFn::new`/datatype constructors that own `new`.
    let Some(set_segment) = path.path.segments.iter().rev().nth(1) else {
        return Ok(None);
    };
    if set_segment.ident != "Set" {
        return Ok(None);
    }
    // `Set::new()` with no args is the empty-set constructor (handled elsewhere).
    if call.args.is_empty() {
        return Ok(None);
    }
    if call.args.len() != 1 {
        return Err(LoweringError::UnsupportedExpr(format!(
            "Set::new expects exactly 1 closure argument, got {}",
            call.args.len()
        )));
    }

    let spec_arg = call.args.first().ok_or_else(|| {
        LoweringError::UnsupportedExpr("Set::new expects a SpecFn::new(...) argument".to_string())
    })?;
    // Normalize a bare closure into an implicit `SpecFn::new(...)`. `Set::new`'s
    // element type is *defined by* the closure parameter, so there is no
    // expected-type hint: the binder must be explicitly annotated (or the arg an
    // explicit `SpecFn::new(...)`), otherwise this fails closed below.
    let spec_fn = lower_spec_fn_arg(spec_arg, env, depth, None)?;
    let TrustVcExpr::SpecClosure { params, ty, .. } = &spec_fn else {
        return Err(LoweringError::UnsupportedExpr(
            "Set::new expects SpecFn::new(...) as its argument".to_string(),
        ));
    };
    let [(_, param_ty)] = params.as_slice() else {
        return Err(LoweringError::TypeInference(format!(
            "Set::new requires a unary SpecFn<T, bool>, got {} parameter(s)",
            params.len()
        )));
    };
    let TrustVcType::SpecFn(_, ret_ty) = ty else {
        return Err(LoweringError::TypeInference(
            "Set::new argument did not lower to a SpecFn".to_string(),
        ));
    };
    if ret_ty.as_ref() != &TrustVcType::Bool {
        return Err(LoweringError::TypeInference(format!(
            "Set::new requires SpecFn<{}, bool>, got predicate returning '{}'",
            param_ty.to_type_string(),
            ret_ty.to_type_string()
        )));
    }

    // Element type: closure parameter type, cross-checked against an explicit
    // `Set::<T>::new` annotation when present (fail-closed on mismatch).
    let elem_ty = match explicit_set_elem_type(set_segment, env)? {
        Some(explicit_ty) if &explicit_ty != param_ty => {
            return Err(LoweringError::TypeInference(format!(
                "Set::new closure parameter has type '{}', but explicit Set element type is '{}'",
                param_ty.to_type_string(),
                explicit_ty.to_type_string()
            )));
        }
        Some(explicit_ty) => explicit_ty,
        None => param_ty.clone(),
    };

    Ok(Some(TrustVcExpr::FnCall {
        name: crate::ir_lowering::SET_NEW_BUILTIN.to_string(),
        args: vec![spec_fn],
        return_ty: TrustVcType::Set(Box::new(elem_ty)),
    }))
}

fn explicit_seq_elem_type(
    seq_segment: &syn::PathSegment,
    env: &TypeEnv,
) -> Result<Option<TrustVcType>, LoweringError> {
    let syn::PathArguments::AngleBracketed(args) = &seq_segment.arguments else {
        return Ok(None);
    };
    let mut type_args = args.args.iter().filter_map(|arg| match arg {
        syn::GenericArgument::Type(ty) => Some(ty),
        _ => None,
    });
    let Some(elem_ty) = type_args.next() else {
        return Ok(None);
    };
    if type_args.next().is_some() {
        return Err(LoweringError::TypeInference(
            "Seq::from_fn/Seq::new expects Seq to have exactly one type argument".into(),
        ));
    }
    env.resolve_syn_type(elem_ty).map(Some)
}

/// Resolve an explicit `Set::<T>` element type argument, if the receiver path
/// segment carries one. Returns `None` for the unannotated `Set::new(...)` form.
fn explicit_set_elem_type(
    set_segment: &syn::PathSegment,
    env: &TypeEnv,
) -> Result<Option<TrustVcType>, LoweringError> {
    let syn::PathArguments::AngleBracketed(args) = &set_segment.arguments else {
        return Ok(None);
    };
    let mut type_args = args.args.iter().filter_map(|arg| match arg {
        syn::GenericArgument::Type(ty) => Some(ty),
        _ => None,
    });
    let Some(elem_ty) = type_args.next() else {
        return Ok(None);
    };
    if type_args.next().is_some() {
        return Err(LoweringError::TypeInference(
            "Set::new expects Set to have exactly one type argument".into(),
        ));
    }
    env.resolve_syn_type(elem_ty).map(Some)
}

fn lower_result_projection_shim_call(
    name: &str,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let variant = match name.rsplit("::").next() {
        Some("__trust_vc_result_ok_0") => "Ok",
        Some("__trust_vc_result_err_0") => "Err",
        _ => return Ok(None),
    };
    if call.args.len() != 1 {
        return Err(LoweringError::UnsupportedExpr(format!(
            "{name} expects 1 argument, got {}",
            call.args.len()
        )));
    }
    let receiver_arg = call.args.first().ok_or_else(|| {
        LoweringError::UnsupportedExpr(format!(
            "{name} expects 1 argument, got {}",
            call.args.len()
        ))
    })?;
    let receiver = lower_syn_expr_with_depth(receiver_arg, env, depth)?;
    let receiver_ty = infer_expr_type(&receiver);
    let TrustVcType::Datatype {
        name: datatype_name,
        variants,
    } = &receiver_ty
    else {
        return Err(LoweringError::TypeInference(format!(
            "Result projection '{variant}_0' requires a Result receiver, got '{}'",
            receiver_ty.to_type_string()
        )));
    };
    if !datatype_name.starts_with("Result<") {
        return Err(LoweringError::TypeInference(format!(
            "Result projection '{variant}_0' requires a Result receiver, got '{}'",
            receiver_ty.to_type_string()
        )));
    }
    let variant_meta = variants
        .iter()
        .find(|candidate| candidate.name == variant)
        .ok_or_else(|| {
            LoweringError::TypeInference(format!(
                "Result projection references missing variant '{variant}' on '{}'",
                receiver_ty.to_type_string()
            ))
        })?;
    let (field_name, field_ty) = variant_meta.fields.first().ok_or_else(|| {
        LoweringError::TypeInference(format!(
            "Result projection '{variant}_0' requires a unary variant"
        ))
    })?;
    if let Some(payload) = direct_result_variant_payload(&receiver, datatype_name, variant) {
        return Ok(Some(payload));
    }
    Ok(Some(TrustVcExpr::FnCall {
        name: selector_symbol_name(datatype_name, variant, field_name, 0),
        args: vec![receiver],
        return_ty: field_ty.clone(),
    }))
}

/// Lowers the general `EXPR->FIELD` field-projection marker
/// (`__trust_vc_field_proj_{field}`) emitted by the variant-DSL rewrite. Resolves
/// the marker to the native selector of the (unique) variant that owns `FIELD` —
/// the native datatype selector is total-but-unconstrained off its constructor,
/// which is the SOUND value when the receiver is a different variant.
fn lower_field_projection_shim_call(
    name: &str,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let short = name.rsplit("::").next().unwrap_or(name);
    let Some(encoded_field) = short.strip_prefix("__trust_vc_field_proj_") else {
        return Ok(None);
    };
    let field = decode_projection_field(encoded_field)?;
    if call.args.len() != 1 {
        return Err(LoweringError::UnsupportedExpr(format!(
            "{name} expects 1 argument, got {}",
            call.args.len()
        )));
    }
    let receiver_arg = call
        .args
        .first()
        .ok_or_else(|| LoweringError::UnsupportedExpr(format!("{name} expects 1 argument")))?;
    let receiver = lower_syn_expr_with_depth(receiver_arg, env, depth)?;
    let receiver_ty = infer_expr_type(&receiver);
    let TrustVcType::Datatype {
        name: datatype_name,
        variants,
    } = &receiver_ty
    else {
        return Err(LoweringError::TypeInference(format!(
            "field projection `->{field}` requires a datatype receiver, got '{}'",
            receiver_ty.to_type_string()
        )));
    };
    // Verus accepts both an unqualified field (`e->v`, or the unique tuple
    // shortcut `e->0`) and the generated variant-qualified spelling
    // (`e->That_v`, `e->A_0`, `option->Some_0`).  The latter is essential when
    // multiple variants own a same-named/tuple-index field.  Collect both
    // interpretations and require one unique native selector.
    let mut owners: Vec<(String, String, usize, TrustVcType)> = Vec::new();
    for variant in variants {
        for (index, (field_name, field_ty)) in variant.fields.iter().enumerate() {
            let exact = field_name == &field;
            let qualified = field
                .strip_prefix(&format!("{}_", variant.name))
                .is_some_and(|suffix| suffix == field_name);
            if exact || qualified {
                let duplicate =
                    owners
                        .iter()
                        .any(|(owner_variant, owner_field, owner_index, _)| {
                            owner_variant == &variant.name
                                && owner_field == field_name
                                && *owner_index == index
                        });
                if !duplicate {
                    owners.push((
                        variant.name.clone(),
                        field_name.clone(),
                        index,
                        field_ty.clone(),
                    ));
                }
            }
        }
    }
    let mut owners = owners.into_iter();
    let Some((variant, field_name, field_index, field_ty)) = owners.next() else {
        return Err(LoweringError::TypeInference(format!(
            "field projection `->{field}` matches no variant field of '{}'",
            receiver_ty.to_type_string()
        )));
    };
    if owners.next().is_some() {
        return Err(LoweringError::TypeInference(format!(
            "field projection `->{field}` is ambiguous across variants of '{}'",
            receiver_ty.to_type_string()
        )));
    }
    if let Some(payload) = direct_result_variant_payload(&receiver, datatype_name, &variant) {
        return Ok(Some(payload));
    }
    Ok(Some(TrustVcExpr::FnCall {
        name: selector_symbol_name(datatype_name, &variant, &field_name, field_index),
        args: vec![receiver],
        return_ty: field_ty,
    }))
}

fn decode_projection_field(encoded: &str) -> Result<String, LoweringError> {
    // The current parser emits `x` followed by lowercase UTF-8 hex. These
    // markers are internal to one parse/lower operation, so accepting an old
    // plain suffix would only create ambiguity with encoded spellings.
    let Some(hex) = encoded.strip_prefix('x') else {
        return Err(LoweringError::UnsupportedExpr(format!(
            "malformed internal field-projection marker `{encoded}`"
        )));
    };
    if hex.len() % 2 != 0 {
        return Err(LoweringError::UnsupportedExpr(format!(
            "malformed internal field-projection marker `{encoded}`"
        )));
    }
    let mut bytes = Vec::with_capacity(hex.len() / 2);
    for &[high_byte, low_byte] in hex.as_bytes().as_chunks::<2>().0 {
        let high = decode_hex_nibble(high_byte);
        let low = decode_hex_nibble(low_byte);
        let (Some(high), Some(low)) = (high, low) else {
            return Err(LoweringError::UnsupportedExpr(format!(
                "malformed internal field-projection marker `{encoded}`"
            )));
        };
        bytes.push((high << 4) | low);
    }
    String::from_utf8(bytes).map_err(|_| {
        LoweringError::UnsupportedExpr(format!(
            "malformed UTF-8 in internal field-projection marker `{encoded}`"
        ))
    })
}

fn decode_hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

fn direct_result_variant_payload(
    receiver: &TrustVcExpr,
    datatype_name: &str,
    variant: &str,
) -> Option<TrustVcExpr> {
    let TrustVcExpr::FnCall {
        name,
        args,
        return_ty,
    } = receiver
    else {
        return None;
    };
    let TrustVcType::Datatype {
        name: receiver_datatype,
        ..
    } = return_ty
    else {
        return None;
    };
    if receiver_datatype != datatype_name || name != &variant_symbol_name(datatype_name, variant) {
        return None;
    }
    let [payload] = args.as_slice() else {
        return None;
    };
    Some(payload.clone())
}

fn lower_wrapping_free_function_call(
    name: &str,
    args: Vec<TrustVcExpr>,
    env: &TypeEnv,
) -> Option<TrustVcExpr> {
    let op = match name {
        "add" => ArithOp::Add,
        "sub" => ArithOp::Sub,
        "mul" => ArithOp::Mul,
        _ => return None,
    };
    if env.lookup_fn(name).is_some() || env.lookup(name).is_some() {
        return None;
    }
    let [left, right] = <[TrustVcExpr; 2]>::try_from(args).ok()?;
    let left_ty = infer_expr_type(&left);
    let right_ty = infer_expr_type(&right);
    let left = coerce_unsuffixed_literal(left, &right_ty);
    let right = coerce_unsuffixed_literal(right, &left_ty);
    let ty = infer_expr_type(&left);
    let coerced_right_ty = infer_expr_type(&right);
    // Verus builtin `add`/`sub`/`mul` over the unbounded math sorts (`int`,
    // `nat`) is the *exact* mathematical operation — truncation only exists
    // for fixed-width operands. Lower to the same plain `Arith` node as the
    // corresponding `+`/`-`/`*`, typed `int`: Verus types these builtins'
    // results as the coerced common `int` for math operands, and `sub` over
    // `nat` can be negative, so the result must not carry a `nat` invariant.
    // (Upstream `nonlinear.rs::test_new_vars`: `mul(x as nat, 2)`. #2778)
    let is_math = |t: &TrustVcType| matches!(t, TrustVcType::MathInt | TrustVcType::Nat);
    if is_math(&ty) && is_math(&coerced_right_ty) {
        return Some(TrustVcExpr::Arith {
            op,
            left: Box::new(left),
            right: Box::new(right),
            ty: TrustVcType::MathInt,
        });
    }
    if !ty.is_integer() || coerced_right_ty != ty {
        return None;
    }
    Some(TrustVcExpr::WrappingArith {
        mode: WrappingMode::Wrapping,
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    })
}

fn lower_explicit_builtin_constructor_call(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(last) = path.path.segments.last() else {
        return Ok(None);
    };
    let variant = last.ident.to_string();
    match variant.as_str() {
        "Some" => {
            let Some(inner_ty) = option_inner_from_path(&path.path, env)? else {
                return Ok(None);
            };
            if call.args.len() != 1 {
                return Err(LoweringError::TypeInference(format!(
                    "constructor 'Some' expects 1 argument, got {}",
                    call.args.len()
                )));
            }
            let option_ty = option_type(inner_ty.clone());
            let arg_expr = call.args.first().ok_or_else(|| {
                LoweringError::TypeInference(format!(
                    "constructor 'Some' expects 1 argument, got {}",
                    call.args.len()
                ))
            })?;
            let arg = lower_syn_expr_with_depth(arg_expr, env, depth)?;
            let arg = coerce_unsuffixed_literal(arg, &inner_ty);
            Ok(Some(datatype_constructor_expr(
                &option_ty,
                "Some",
                vec![arg],
            )?))
        }
        "Ok" | "Err" => {
            let Some((ok_ty, err_ty)) = result_types_from_path(&path.path, env)? else {
                return Ok(None);
            };
            if call.args.len() != 1 {
                return Err(LoweringError::TypeInference(format!(
                    "constructor '{}' expects 1 argument, got {}",
                    variant,
                    call.args.len()
                )));
            }
            let result_ty = result_type(ok_ty.clone(), err_ty.clone());
            let field_ty = if variant == "Ok" { &ok_ty } else { &err_ty };
            let arg_expr = call.args.first().ok_or_else(|| {
                LoweringError::TypeInference(format!(
                    "constructor '{}' expects 1 argument, got {}",
                    variant,
                    call.args.len()
                ))
            })?;
            let arg = lower_syn_expr_with_depth(arg_expr, env, depth)?;
            let arg = coerce_unsuffixed_literal(arg, field_ty);
            Ok(Some(datatype_constructor_expr(
                &result_ty,
                &variant,
                vec![arg],
            )?))
        }
        _ => Ok(None),
    }
}

fn lower_default_constructor_call(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    if !call.args.is_empty() || !path_matches_suffix(&path.path, &["default"]) {
        return Ok(None);
    }
    // A QUALIFIED spelling that still reaches the lowering (`<Ty>::default()`
    // / `<Ty as Default>::default()`; the extraction normally renders these
    // away) names its type in the qself: read it from there.
    if path.qself.is_some() {
        if !crate::default_constructor::qself_call_is_default_constructor(path) {
            return Ok(None);
        }
        let Some(qself) = path.qself.as_ref() else {
            return Ok(None);
        };
        return lower_default_of_syn_type(&qself.ty, env, depth);
    }
    let Some(receiver_segment) = path.path.segments.iter().rev().nth(1) else {
        return Ok(None);
    };

    let receiver = receiver_segment.ident.to_string();
    // Rust's `Default` impl for every fixed-width primitive integer is
    // definitionally `0` (and `isize`/`usize`). The primitive type name is also
    // its literal-suffix spelling, so `type_from_int_suffix` yields the exact
    // signed/unsigned + width mapping. This is sound: a fixed `0` is at least as
    // conservative as Verus, which assigns the same value (see
    // ../verus/source/rust_verify_test/tests/default_trait.rs). We restrict to
    // the concrete machine-integer spellings — the ghost types `int`/`nat`/`real`
    // and the empty suffix are NOT constructible via `Default` in Rust source, so
    // they stay fail-closed (handled by the catch-all below).
    if matches!(receiver_segment.arguments, syn::PathArguments::None)
        && matches!(
            receiver.as_str(),
            "i8" | "i16"
                | "i32"
                | "i64"
                | "i128"
                | "isize"
                | "u8"
                | "u16"
                | "u32"
                | "u64"
                | "u128"
                | "usize"
        )
    {
        let ty = super::super::type_from_int_suffix(&receiver)?;
        return Ok(Some(TrustVcExpr::IntLit { value: 0, ty }));
    }

    match receiver.as_str() {
        "bool" if matches!(receiver_segment.arguments, syn::PathArguments::None) => {
            Ok(Some(TrustVcExpr::BoolLit(false)))
        }
        "Option" => {
            let Some(inner_ty) = option_inner_from_path(&path.path, env)? else {
                return Ok(None);
            };
            let option_ty = option_type(inner_ty);
            Ok(Some(datatype_constructor_expr(&option_ty, "None", vec![])?))
        }
        // Every other receiver spelling — `f32::default()`, `char::default()`,
        // `String::default()`, `<&str>` (rendered `str::default()` by the
        // extraction), `Vec::<T>::default()`, `VecDeque::<T>::default()`,
        // `HashMap::<K, V>::default()` / `HashSet::<T>::default()`,
        // `Box::<T>::default()` / `Rc` / `Arc`, `PhantomData::<T>::default()` —
        // is read as a TYPE (the turbofish becomes the type's arguments) and
        // lowered as the source the shared `default_constructor` model spells
        // for it. A user type or a type parameter spells as its own
        // `Ty::default()` and is declined here, so it resolves ONLY through a
        // registered symbol (an `impl Default` body axiom, a
        // `#[derive(Default)]`-synthesized body, the per-type-parameter
        // constant) and otherwise keeps the "unknown return type" refusal.
        _ => {
            let Some(receiver_ty) =
                crate::default_constructor::default_receiver_syn_type(&path.path)
            else {
                return Ok(None);
            };
            lower_default_of_syn_type(&receiver_ty, env, depth)
        }
    }
}

/// Lower the default value of `ty` through its source-level model, or
/// `Ok(None)` when the model spells nothing for it (or spells a user-type /
/// type-parameter receiver call, which the registered-symbol path owns).
fn lower_default_of_syn_type(
    ty: &syn::Type,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(source) = crate::default_constructor::default_value_source_for_type(ty) else {
        return Ok(None);
    };
    if crate::default_constructor::source_is_receiver_default_call(&source) {
        return Ok(None);
    }
    let expr: syn::Expr = syn::parse_str(&source).map_err(|err| {
        LoweringError::TypeInference(format!(
            "default constructor model for '{}' did not parse: {err}",
            quote::quote!(#ty).to_string().replace(' ', "")
        ))
    })?;
    lower_syn_expr_with_depth(&expr, env, depth).map(Some)
}

fn lower_cow_constructor_call(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(last) = path.path.segments.last() else {
        return Ok(None);
    };
    let variant = last.ident.to_string();
    if !matches!(variant.as_str(), "Owned" | "Borrowed") || !path_has_cow_segment(&path.path) {
        return Ok(None);
    }
    if call.args.len() != 1 {
        return Err(LoweringError::TypeInference(format!(
            "constructor 'Cow::{}' expects 1 argument, got {}",
            variant,
            call.args.len()
        )));
    }

    let arg_expr = call.args.first().ok_or_else(|| {
        LoweringError::TypeInference(format!(
            "constructor 'Cow::{}' expects 1 argument, got {}",
            variant,
            call.args.len()
        ))
    })?;
    let arg = lower_syn_expr_with_depth(arg_expr, env, depth)?;
    let inner_ty = cow_inner_from_path(&path.path, env)?.unwrap_or_else(|| infer_expr_type(&arg));
    let cow_ty = cow_type(inner_ty.clone());
    let arg = coerce_unsuffixed_literal(arg, &inner_ty);
    Ok(Some(datatype_constructor_expr(
        &cow_ty,
        &variant,
        vec![arg],
    )?))
}

fn path_has_cow_segment(path: &syn::Path) -> bool {
    path.segments.iter().any(|segment| segment.ident == "Cow")
}

fn cow_inner_from_path(
    path: &syn::Path,
    env: &TypeEnv,
) -> Result<Option<TrustVcType>, LoweringError> {
    let Some(cow_segment) = path.segments.iter().find(|segment| segment.ident == "Cow") else {
        return Ok(None);
    };
    let syn::PathArguments::AngleBracketed(args) = &cow_segment.arguments else {
        return Ok(None);
    };
    let type_args = args
        .args
        .iter()
        .filter_map(|arg| match arg {
            syn::GenericArgument::Type(ty) => Some(ty),
            _ => None,
        })
        .collect::<Vec<_>>();
    match type_args.as_slice() {
        [inner_ty] => Ok(Some(trust_vc_type_from_syn_type_with_env(inner_ty, env)?)),
        [] => Ok(None),
        _ => Err(LoweringError::TypeInference(
            "Cow constructor supports exactly one verification-relevant type argument".into(),
        )),
    }
}

fn lower_inferred_some_constructor_call(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(last) = path.path.segments.last() else {
        return Ok(None);
    };
    if path.path.segments.len() != 1 || last.ident != "Some" || call.args.len() != 1 {
        return Ok(None);
    }
    if env.lookup_variants("Some").is_some_and(|variants| {
        variants
            .iter()
            .any(|variant| !is_option_type_name(&variant.datatype_name))
    }) {
        return Ok(None);
    }
    let Some(arg_expr) = call.args.first() else {
        return Ok(None);
    };
    let arg = lower_syn_expr_with_depth(arg_expr, env, depth)?;
    let inner_ty = infer_expr_type(&arg);
    let option_ty = option_type(inner_ty);
    Ok(Some(datatype_constructor_expr(
        &option_ty,
        "Some",
        vec![arg],
    )?))
}

fn is_option_type_name(name: &str) -> bool {
    name.starts_with("Option<")
}

fn option_inner_from_path(
    path: &syn::Path,
    env: &TypeEnv,
) -> Result<Option<TrustVcType>, LoweringError> {
    if let Some(last) = path.segments.last() {
        if last.ident == "Some" {
            if let syn::PathArguments::AngleBracketed(args) = &last.arguments {
                return Ok(Some(generic_type_arg(args, 0, env)?));
            }
        }
    }
    let Some(option_segment) = path.segments.iter().rev().nth(1) else {
        return Ok(None);
    };
    if option_segment.ident != "Option" {
        return Ok(None);
    }
    let syn::PathArguments::AngleBracketed(args) = &option_segment.arguments else {
        return Ok(None);
    };
    Ok(Some(generic_type_arg(args, 0, env)?))
}

fn result_types_from_path(
    path: &syn::Path,
    env: &TypeEnv,
) -> Result<Option<(TrustVcType, TrustVcType)>, LoweringError> {
    if let Some(last) = path.segments.last() {
        if matches!(last.ident.to_string().as_str(), "Ok" | "Err") {
            if let syn::PathArguments::AngleBracketed(args) = &last.arguments {
                return Ok(Some((
                    generic_type_arg(args, 0, env)?,
                    generic_type_arg(args, 1, env)?,
                )));
            }
        }
    }
    let Some(result_segment) = path.segments.iter().rev().nth(1) else {
        return Ok(None);
    };
    if result_segment.ident != "Result" {
        return Ok(None);
    }
    let syn::PathArguments::AngleBracketed(args) = &result_segment.arguments else {
        return Ok(None);
    };
    Ok(Some((
        generic_type_arg(args, 0, env)?,
        generic_type_arg(args, 1, env)?,
    )))
}

fn generic_type_arg(
    args: &syn::AngleBracketedGenericArguments,
    index: usize,
    env: &TypeEnv,
) -> Result<TrustVcType, LoweringError> {
    let ty = args
        .args
        .iter()
        .filter_map(|arg| match arg {
            syn::GenericArgument::Type(ty) => Some(ty),
            _ => None,
        })
        .nth(index)
        .ok_or_else(|| {
            LoweringError::TypeInference(format!(
                "builtin constructor is missing type argument {}",
                index + 1
            ))
        })?;
    trust_vc_type_from_syn_type_with_env(ty, env)
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

fn cow_type(inner_ty: TrustVcType) -> TrustVcType {
    TrustVcType::Datatype {
        name: format!("Cow<{}>", inner_ty.to_type_string()),
        variants: vec![
            DatatypeVariant::new("Borrowed", vec![("0".to_string(), inner_ty.clone())]),
            DatatypeVariant::new("Owned", vec![("0".to_string(), inner_ty)]),
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
            "builtin constructor did not produce a datatype".into(),
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
    Ok(TrustVcExpr::FnCall {
        name: variant_symbol_name(name, variant),
        args,
        return_ty: datatype_ty.clone(),
    })
}

fn path_matches_suffix(path: &syn::Path, suffix: &[&str]) -> bool {
    let segments: Vec<_> = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect();
    let suffix: Vec<_> = suffix.iter().map(|segment| segment.to_string()).collect();
    segments.ends_with(&suffix)
}

fn lower_prophecy_new_call(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
) -> Result<TrustVcExpr, LoweringError> {
    if !call.args.is_empty() {
        return Err(LoweringError::UnsupportedExpr(format!(
            "Proph::new expects 0 args, got {}",
            call.args.len()
        )));
    }
    let ty = proph_new_inner_type(&path.path, env)?;
    Ok(TrustVcExpr::ProphecyNew {
        name: "__trust_vc_prophecy_unbound__".to_string(),
        ty,
    })
}

fn proph_new_inner_type(path: &syn::Path, env: &TypeEnv) -> Result<TrustVcType, LoweringError> {
    let proph_segment =
        path.segments.iter().rev().nth(1).ok_or_else(|| {
            LoweringError::TypeInference("Proph::new missing Proph segment".into())
        })?;
    let syn::PathArguments::AngleBracketed(args) = &proph_segment.arguments else {
        return Err(LoweringError::TypeInference(
            "Proph::new requires explicit type parameter, e.g. Proph::<u64>::new()".into(),
        ));
    };
    let Some(syn::GenericArgument::Type(inner_ty)) = args.args.first() else {
        return Err(LoweringError::TypeInference(
            "Proph::new requires a concrete inner type".into(),
        ));
    };
    trust_vc_type_from_syn_type_with_env(inner_ty, env)
}

/// Lower `Type::singleton(v)` as `Type::empty().insert(v)`.
///
/// Keeps `constructors.rs` zero-arity-only: singleton is lowering sugar,
/// not a new collection constructor path. Fixes #2604.
fn lower_collection_singleton(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(last_segment) = path.path.segments.last() else {
        return Ok(None);
    };
    if last_segment.ident != "singleton" {
        return Ok(None);
    }

    // Build a modified path replacing "singleton" with "empty"
    let mut empty_path = path.clone();
    let Some(last) = empty_path.path.segments.last_mut() else {
        return Ok(None);
    };
    last.ident = syn::Ident::new("empty", last.ident.span());
    last.arguments = syn::PathArguments::None;

    // Reuse existing zero-arity constructor lowering
    let empty_constructor = match lower_collection_constructor(&empty_path, env)? {
        Some(expr) => expr,
        None => return Ok(None),
    };

    let (collection_ty, constructor_name) = match &empty_constructor {
        TrustVcExpr::FnCall {
            return_ty, name, ..
        } => (return_ty.clone(), name.clone()),
        _ => return Ok(None),
    };

    // Lower the singleton argument
    let Some(arg_expr) = call.args.first() else {
        return Ok(None);
    };
    let arg = lower_syn_expr_with_depth(arg_expr, env, depth)?;

    Ok(Some(TrustVcExpr::CollectionOp {
        op: CollectionOp::Insert,
        receiver: Box::new(empty_constructor),
        receiver_name: Some(constructor_name),
        args: vec![arg],
        ty: collection_ty,
    }))
}
