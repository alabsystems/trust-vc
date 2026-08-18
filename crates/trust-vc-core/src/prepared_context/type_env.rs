//! Type-environment construction for prepared contexts.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::error::TrustVcError;
use crate::ir::{TraitBound, TraitDecl};
use crate::ir_lowering::{MethodMeta, TypeEnv};
use crate::vc::VerificationContext;

pub(crate) fn build_type_env(ctx: &VerificationContext) -> Result<TypeEnv, TrustVcError> {
    let mut env = TypeEnv::new();
    for (name, ty) in ctx.source_type_aliases() {
        // A generic enum TEMPLATE carrier (its fields mention a `TypeParam`) is
        // registered as a resolvable alias but WITHOUT datatype variant
        // metadata: the usable constructor/selector metadata comes from the
        // concrete per-instantiation carrier (`GList<i32>`), and registering the
        // template too (same base name `GList`) would make every qualified
        // `GList::GCons` constructor path ambiguous.
        if ty.contains_type_param() {
            env.insert_type_alias_without_metadata(name.clone(), ty.clone());
        } else {
            env.insert_type_alias(name.clone(), ty.clone());
        }
    }
    for variable in &ctx.variables {
        env.insert(variable.name.clone(), variable.ty.clone());
        if ctx.erased_shared_ref_vars.contains(&variable.name) {
            env.insert_erased_shared_ref_var(variable.name.clone());
        }
        if ctx.erased_ghost_vars.contains(&variable.name) {
            env.insert_erased_ghost_var(variable.name.clone());
        }
    }
    for (name, ty) in ctx.prophecy_bindings() {
        env.insert_prophecy_binding(name.clone(), ty.clone());
    }
    for struct_def in &ctx.struct_types {
        env.register_type_metadata_only(&struct_def.to_datatype_type());
    }
    // Structs AND enums that derived PartialEq/Clone — so `.eq()`/`.clone()` may
    // lower structurally for them (see `is_structural_eq_type`/`clone_type`).
    for name in &ctx.derived_partial_eq_types {
        env.register_derived_partial_eq(name.clone());
    }
    for name in &ctx.derived_clone_types {
        env.register_derived_clone(name.clone());
    }
    // Datatypes with a hand-written `impl PartialEq` — the `==`/`!=` operator on
    // them must NOT structural-lower (their exec `==` may be non-structural).
    for name in &ctx.manual_partial_eq_types {
        env.register_manual_partial_eq(name.clone());
    }

    // Register function context names so obligation conditions can reference them.
    // Zero-arity functions act as variables; N-arity functions are uninterpreted
    // functions that may appear as bare identifiers in conditions. Both need to
    // be in the TypeEnv for lowering to resolve. (Part of #1927)
    if let Some(ref function_context) = ctx.function_context {
        if function_context.return_type.contains_opaque() {
            return Err(TrustVcError::Encoding {
                context: "validate function context",
                detail: format!(
                    "invalid return type '{}' for function '{}'",
                    function_context.return_type.to_type_string(),
                    function_context.name
                ),
            });
        }
        env.insert_fn(
            function_context.name.clone(),
            function_context.return_type.clone(),
        );
        let param_types: Vec<_> = function_context
            .params
            .iter()
            .map(|(_, ty)| ty.clone())
            .collect();
        env.insert_fn_params(function_context.name.clone(), param_types);
    }

    // Register helper/broadcast function return types so obligation conditions
    // referencing them can be lowered. Without this, `lower_call` errors with
    // "unknown return type for function". Fixes #2173.
    for (name, return_type_str) in &ctx.helper_functions {
        let return_ty = crate::ir::TrustVcType::try_from_str(return_type_str).map_err(|err| {
            TrustVcError::Encoding {
                context: "validate helper function",
                detail: format!(
                    "invalid return type '{}' for helper function '{}': {}",
                    return_type_str, name, err
                ),
            }
        })?;
        env.insert_fn(name.clone(), return_ty);
    }

    // Register typed helper functions (supports TypeParam return types).
    // These come from spec expansion's proof_mode_block and include all
    // called spec functions, not just the last one (which overwrites
    // function_context). Part of #2431.
    for (name, (return_ty, params, _bounds)) in &ctx.helper_functions_typed {
        env.insert_fn(name.clone(), return_ty.clone());
        let param_types: Vec<_> = params.iter().map(|(_, ty)| ty.clone()).collect();
        env.insert_fn_params(name.clone(), param_types);
    }

    register_trait_bound_methods(&mut env, ctx)?;

    // Register inherent-impl method metadata so `recv.method(args)` in a spec
    // context resolves to the typed UF call. The companion `Type::method` /
    // `Self::method` associated-call symbols are registered through
    // `helper_functions_typed` above. Part of A3.
    for ((self_type, method_name), (uf_name, return_type, param_types)) in &ctx.inherent_methods {
        let meta = MethodMeta {
            uf_name: uf_name.clone(),
            return_type: return_type.clone(),
            param_types: param_types.clone(),
            box_receiver: None,
        };
        register_method_metadata(&mut env, self_type, method_name, meta)?;
    }

    // Concrete-impl trait methods: a call on a CONCRETE receiver (`s.g()` where
    // `impl Tr for S`) resolves to the SAME trait UF + contract axiom as the
    // generic path, with the receiver boxed into `Poly`. Slice 1 of #33.
    //
    // Registered LAST and fail-SAFE (never propagates a conflict error, never
    // overrides an existing binding): datatype accessors, inherent methods, and
    // generic trait-bound methods all take precedence — matching Rust, where an
    // inherent method shadows a trait method of the same name.
    register_trait_impl_methods_for_concrete_types(&mut env, ctx);

    Ok(env)
}

fn register_trait_bound_methods(
    env: &mut TypeEnv,
    ctx: &VerificationContext,
) -> Result<(), TrustVcError> {
    if let Some(function_context) = &ctx.function_context {
        register_trait_bound_methods_for_bounds(
            env,
            &ctx.trait_decls,
            &function_context.trait_bounds,
        )?;
    }

    // Helper spec functions can carry their own trait bounds, and their body
    // axioms are lowered through the same shared TypeEnv. Register those bound
    // methods here so `prepare_context()` can lower helper bodies like
    // `helper(x) == x.method()` even when the primary function_context is a
    // different function with no matching bounds. Part of #2425.
    for (_return_ty, _params, bounds) in ctx.helper_functions_typed.values() {
        register_trait_bound_methods_for_bounds(env, &ctx.trait_decls, bounds)?;
    }

    Ok(())
}

fn register_trait_bound_methods_for_bounds(
    env: &mut TypeEnv,
    trait_decls: &[TraitDecl],
    bounds: &[TraitBound],
) -> Result<(), TrustVcError> {
    for bound in bounds {
        // Register the bound trait's OWN methods AND its (transitive) supertrait
        // methods on the bound's type parameter. A `T: Ext` bound where
        // `Ext: Base` implies `T: Base`, so `x.base()` for `x: T` is a valid call
        // and must resolve to `Base__base` — grounded by Base's own postcondition
        // axiom (emitted when Base is registered). Reuses the same start-first BFS
        // (shadowing + cycle-safe) the caller-side requires discharge uses, so the
        // method-resolution closure and the requires closure cannot drift.
        for (declaring_trait, method) in
            crate::vc_extraction::trait_contracts::supertrait_closure_methods(
                trait_decls,
                &bound.trait_name,
            )
        {
            let meta = MethodMeta {
                uf_name: format!("{}__{}", declaring_trait, method.name),
                return_type: method.return_type.clone(),
                param_types: method.params.iter().map(|(_, ty)| ty.clone()).collect(),
                box_receiver: None,
            };
            register_method_metadata(env, &bound.type_param, &method.name, meta)?;
        }
    }

    Ok(())
}

/// Registers concrete-impl trait methods so a spec-context call on a CONCRETE
/// receiver (`s.g()` where `s: S` and `impl Tr for S`) resolves to the SAME
/// trait UF (`Tr__g`) as the generic path — with the receiver boxed into `Poly`.
///
/// Slice 1 of #33 (concrete-impl trait-method VALUE resolution). This mirrors
/// [`register_trait_bound_methods_for_bounds`] but keys the metadata on the
/// concrete type name (matching how `dispatch/methods.rs` computes `type_name`
/// from the receiver via `to_type_string()`) and records `box_receiver =
/// Some("Box_T")` so the receiver is lifted into the trait UF's `Poly`
/// self-domain. The resulting term `Tr__g(Box_S(s))` is discharged by the
/// trait's already-emitted postcondition axiom (the declared contract) — the
/// impl BODY is NOT emitted as a value axiom here (that is Slice 2).
///
/// SOUNDNESS: fails closed rather than register when it cannot guarantee a sound
/// resolution:
/// * the concrete type must resolve to a fully-concrete registered struct
///   datatype (so its `Box_S` bridge is declared by `register_trait_impl` and
///   its sort exists) — an unresolved/opaque type is skipped, leaving the
///   existing "method not available in spec context" error;
/// * every method param type and the return type must be fully concrete (no
///   `TypeParam`/`Poly`/opaque) so the boxed application sort-checks and no
///   `Self`-typed value escapes unboxed — otherwise that method is skipped.
///
/// * an AMBIGUOUS method — the same method name reachable through two different
///   trait impls on one concrete type (`impl A for S` and `impl B for S`, both
///   declaring `m`) — is NOT registered, so `s.m()` stays fail-closed (Verus
///   also rejects the ambiguity); and
/// * an existing binding (datatype accessor, inherent method, generic bound)
///   is never overridden — inherent methods shadow trait methods, as in Rust.
///
/// This function is INFALLIBLE and purely additive: it never propagates a
/// conflict error (which would taint the whole `build_type_env` and sink every
/// unrelated function in the file). Registering LESS than possible is fine
/// (fail-closed); registering an unsound resolution is forbidden.
fn register_trait_impl_methods_for_concrete_types(env: &mut TypeEnv, ctx: &VerificationContext) {
    use std::collections::{HashMap, HashSet};

    // Collect candidate (concrete_type, method) -> meta registrations, detecting
    // cross-impl ambiguity (same key, differing meta) so it can be dropped
    // wholesale rather than resolved to an arbitrary impl.
    let mut candidates: HashMap<(String, String), MethodMeta> = HashMap::new();
    let mut ambiguous: HashSet<(String, String)> = HashSet::new();

    for impl_decl in &ctx.trait_impl_decls {
        // Resolve the concrete self type to a fully-concrete registered struct
        // datatype, mirroring `resolve_trait_impl_concrete_types`. Only then is
        // its `Box_T`/self sort guaranteed to be declared by the encoder.
        let Some(concrete_type_name) =
            resolvable_concrete_type_name(&impl_decl.concrete_type, &ctx.struct_types)
        else {
            continue;
        };

        let Some(trait_decl) = ctx
            .trait_decls
            .iter()
            .find(|decl| decl.name == impl_decl.trait_name)
        else {
            continue;
        };

        let box_fn = format!("Box_{concrete_type_name}");

        for method in &trait_decl.methods {
            // Instantiate a parameterized trait's bare-TypeParam positions at
            // the impl's trait type args (trait-side A2-generic); identity for
            // fully-concrete signatures. `None` (blanket impl, nested TypeParam
            // position, unbound param, requires-bearing bridged method) is
            // skipped fail-closed — in lockstep with the encoder, which emits a
            // linking axiom for exactly the instantiable set.
            let Some(sig) = crate::trait_instantiation::instantiate_trait_method_sig(
                &trait_decl.generics,
                impl_decl,
                method,
            ) else {
                // The instantiator fails closed on any associated-type-projection
                // position (the shared per-trait UF cannot carry a per-impl
                // projected sort). But a concrete client calling `s.produce()`
                // still needs the call to RESOLVE. Register it against the
                // PER-IMPL concrete function instead (no shared-UF boxing), with
                // the projection resolved to this impl's concrete binding — the
                // concrete-sorted trait-ensures postcondition axiom
                // (`assert_impl_trait_ensures_concrete_axioms`) carries the
                // contract on that same function. Non-generic trait only: a
                // parameterized trait ALSO using assoc types stays fail-closed.
                if let Some((key, meta)) = assoc_concrete_method_candidate(
                    &concrete_type_name,
                    trait_decl,
                    impl_decl,
                    method,
                ) {
                    match candidates.get(&key) {
                        Some(existing) if existing == &meta => {}
                        Some(_) => {
                            ambiguous.insert(key.clone());
                        }
                        None => {
                            candidates.insert(key, meta);
                        }
                    }
                }
                continue;
            };

            // Fail closed on any signature we cannot box soundly: a non-concrete
            // param or return would leave a `Self`/type-param value in a sort
            // that the boxed application cannot honor.
            let signature_is_concrete = std::iter::once(&sig.return_type)
                .chain(sig.params.iter().map(|(ty, _)| ty))
                .all(is_concrete_boxable_type);
            if !signature_is_concrete {
                continue;
            }

            let key = (concrete_type_name.clone(), method.name.clone());
            let meta = MethodMeta {
                uf_name: format!("{}__{}", trait_decl.name, method.name),
                return_type: sig.return_type.clone(),
                param_types: sig.params.iter().map(|(ty, _)| ty.clone()).collect(),
                box_receiver: Some(box_fn.clone()),
            };
            match candidates.get(&key) {
                Some(existing) if existing == &meta => {} // idempotent duplicate
                Some(_) => {
                    ambiguous.insert(key.clone());
                }
                None => {
                    candidates.insert(key, meta);
                }
            }
        }
    }

    for (key, meta) in candidates {
        if ambiguous.contains(&key) {
            continue;
        }
        // Fail SAFE: never override an existing binding (accessor / inherent /
        // generic bound already registered) and never surface a conflict error.
        if env.lookup_method(&key.0, &key.1).is_some() {
            continue;
        }
        env.insert_method_metadata(key.0, key.1, meta);
    }
}

/// Returns the concrete type-string key for a trait-impl self type iff it
/// resolves to a fully-concrete struct datatype (so its `Box_T` bridge and self
/// sort are guaranteed to be declared by `register_trait_impl`). Returns `None`
/// for anything that stays opaque/unresolved, so registration fails closed.
///
/// The returned name is `to_type_string()` of the resolved datatype, which for a
/// struct is its bare name — matching both the box-function key
/// (`ensure_box_unbox` keys on `concrete_type.to_type_string()`) and the
/// `type_name` `dispatch/methods.rs` derives from the receiver.
fn resolvable_concrete_type_name(
    concrete_type: &crate::ir::TrustVcType,
    struct_types: &[crate::ir::StructDef],
) -> Option<String> {
    use crate::ir::TrustVcType;
    match concrete_type {
        TrustVcType::Opaque(name) => {
            let struct_def = struct_types.iter().find(|def| &def.name == name)?;
            let datatype = struct_def.to_datatype_type();
            if datatype.contains_opaque() {
                return None;
            }
            Some(datatype.to_type_string())
        }
        TrustVcType::Datatype { .. } if !concrete_type.contains_opaque() => {
            Some(concrete_type.to_type_string())
        }
        // `impl Tr for S` whose self type is a single-identifier struct name is
        // classified `TypeParam("S")` by the macro-expand heuristic (no struct
        // registry there). Resolve it against the registered structs — a name that
        // IS a concrete struct resolves like the `Opaque` arm; a genuine blanket
        // type param (`impl<A> Tr for A`) matches no struct and stays `None`
        // (fail-closed — a blanket impl is not a concrete receiver).
        TrustVcType::TypeParam(name) => {
            let struct_def = struct_types.iter().find(|def| &def.name == name)?;
            let datatype = struct_def.to_datatype_type();
            if datatype.contains_opaque() {
                return None;
            }
            Some(datatype.to_type_string())
        }
        _ => None,
    }
}

/// True iff `ty` is a fully-concrete type whose backend sort is fixed — i.e. it
/// carries no `TypeParam`, is not the type-erased `Poly` (a `Self`-typed
/// param/return), and contains no opaque component. Used to gate concrete-impl
/// trait-method registration so every boxed application sort-checks.
fn is_concrete_boxable_type(ty: &crate::ir::TrustVcType) -> bool {
    !matches!(ty, crate::ir::TrustVcType::Poly)
        && !ty.contains_type_param()
        && !ty.contains_opaque()
}

/// Client-side resolution for an associated-type-bearing trait method that the
/// generic-bridge instantiator (`instantiate_trait_method_sig`) fail-closes on
/// (the shared per-trait UF cannot carry a per-impl projected sort). Registers
/// the concrete receiver's call directly against the PER-IMPL concrete function
/// named in `impl_decl.method_bindings`, with the method's `Self::Assoc`
/// projections resolved to this impl's concrete bindings, so a caller
/// `s.produce()` lowers to a well-sorted `Impl__produce(s)` (`box_receiver: None`
/// — no shared-UF boxing). The trait contract on that function is supplied
/// separately by `assert_impl_trait_ensures_concrete_axioms`, itself gated by the
/// per-impl conformance pass.
///
/// Returns `None` (fail-closed) unless the signature genuinely projects an
/// associated type this impl resolves FULLY CONCRETE, the method is
/// `requires`-free, and the trait is non-generic (a parameterized trait that
/// ALSO uses associated types stays out of scope). Registering a resolution
/// introduces NO fact on its own — it only lets the call name a declared
/// function — so this widening is sound (completeness only).
fn assoc_concrete_method_candidate(
    concrete_type_name: &str,
    trait_decl: &crate::ir::TraitDecl,
    impl_decl: &crate::ir::TraitImplDecl,
    method: &crate::ir::TraitMethodDecl,
) -> Option<((String, String), MethodMeta)> {
    if !trait_decl.generics.is_empty() || !method.requires.is_empty() {
        return None;
    }
    let has_projection = method
        .params
        .iter()
        .map(|(_, ty)| ty)
        .chain(std::iter::once(&method.return_type))
        .any(|ty| impl_decl.resolve_assoc_projections(ty) != *ty);
    if !has_projection {
        return None;
    }
    let return_type = impl_decl.resolve_assoc_projections(&method.return_type);
    let param_types: Vec<crate::ir::TrustVcType> = method
        .params
        .iter()
        .map(|(_, ty)| impl_decl.resolve_assoc_projections(ty))
        .collect();
    if !is_concrete_boxable_type(&return_type) || !param_types.iter().all(is_concrete_boxable_type)
    {
        return None;
    }
    let concrete_fn = impl_decl
        .method_bindings
        .iter()
        .find(|(trait_method, _)| trait_method == &method.name)
        .map(|(_, concrete_fn)| concrete_fn.clone())?;
    let meta = MethodMeta {
        uf_name: concrete_fn,
        return_type,
        param_types,
        box_receiver: None,
    };
    Some(((concrete_type_name.to_string(), method.name.clone()), meta))
}

fn register_method_metadata(
    env: &mut TypeEnv,
    receiver_type_name: &str,
    method_name: &str,
    meta: MethodMeta,
) -> Result<(), TrustVcError> {
    if let Some(existing) = env.lookup_method(receiver_type_name, method_name) {
        if existing == &meta {
            return Ok(());
        }
        // A user-written inherent method may share its name with an
        // auto-generated datatype accessor — e.g. a hand-written
        // `fn is_A(&self) -> bool` or `fn get_A_0(&self) -> ...` on an enum
        // whose variant `A` already yields the tester `is_A` / selector
        // `get_A_0`. The two `MethodMeta`s differ only in their backing
        // uninterpreted-function symbol, so the generic equality check above
        // does not see them as equal. Rather than fail closed, keep the
        // canonical accessor already registered by
        // `TypeEnv::register_variant_helper_methods`: it carries the encoder's
        // true selector/tester semantics, so any `recv.is_A()` / `recv.get_A_0()`
        // call (and the identically-spelled selector strings the pattern-binding
        // extractor emits for `let`/`let-else`/`match` field projection) resolves
        // to the real datatype accessor. Folding the redundant user declaration
        // into the accessor only ever adds true datatype facts, so it is sound —
        // it cannot turn a violable obligation into a false pass.
        if env.is_auto_accessor_method(receiver_type_name, method_name) {
            return Ok(());
        }
        return Err(TrustVcError::Encoding {
            context: "build type environment",
            detail: format!(
                "conflicting method metadata for '{}.{}'",
                receiver_type_name, method_name
            ),
        });
    }

    env.insert_method_metadata(
        receiver_type_name.to_string(),
        method_name.to_string(),
        meta,
    );
    Ok(())
}
