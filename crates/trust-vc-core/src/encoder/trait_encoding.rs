//! Trait method UF registration and contract axioms.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Slice 2 of trait verification registers one uninterpreted function per
//! trait method over a Poly-typed receiver and emits quantified postcondition
//! axioms guarded by the trait method preconditions.
#![cfg_attr(not(test), allow(dead_code))]

use std::collections::HashMap;

use ay_dpll::api::FuncDecl;

use super::types::sort_for_type;
use super::AYEncoder;
use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::{TraitDecl, TraitImplDecl, TraitMethodDecl, TrustVcType};

#[path = "trait_encoding_axioms.rs"]
mod axioms;

use axioms::{sanitize_symbol, trait_encoding_error, trait_method_symbol};

const TRAIT_ENCODING_CONTEXT: &str = "register trait";
const TRAIT_RECEIVER_NAME: &str = "self";
const TRAIT_RESULT_NAME: &str = "result";
const TRAIT_RECEIVER_TYPE_NAME: &str = "Poly";

#[derive(Debug, Clone)]
pub(crate) struct TraitEncoding {
    pub(crate) name: String,
    pub(crate) method_fns: HashMap<String, FuncDecl>,
    /// Default body text for methods that have default implementations.
    /// Keyed by method name. Used by `register_trait_impl` to emit
    /// per-impl body axioms for inherited (non-overridden) defaults.
    /// Part of #2442.
    default_bodies: HashMap<String, String>,
    /// Method declarations from the TraitDecl, needed by `register_trait_impl`
    /// to build TypeEnv for default body lowering. Part of #2442.
    methods: Vec<TraitMethodDecl>,
    /// Ordered type-parameter names of a parameterized trait; zipped against an
    /// impl's `trait_type_args` to instantiate bare-TypeParam signature slots.
    generics: Vec<String>,
}

impl AYEncoder {
    /// Returns the cached trait encoding, if the trait has been registered.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn trait_encoding(&self, trait_name: &str) -> Option<&TraitEncoding> {
        self.registries.trait_encodings.get(trait_name)
    }

    /// Declares trait method UFs and emits quantified postcondition axioms.
    ///
    /// Idempotent: repeated registration of the same trait name reuses the
    /// cached encoding without re-declaring UFs or re-asserting axioms.
    pub(crate) fn register_trait(&mut self, decl: &TraitDecl) -> TrustVcResult<TraitEncoding> {
        if let Some(existing) = self.registries.trait_encodings.get(&decl.name) {
            // Idempotent ONLY for an equal re-registration. Two DIFFERENT
            // traits colliding on one name would silently share one UF set and
            // one axiom set (a name-collapse false-verify vector) — fail the
            // file closed instead.
            if existing.methods == decl.methods && existing.generics == decl.generics {
                return Ok(existing.clone());
            }
            return Err(trait_encoding_error(format!(
                "trait name collision: '{}' is already registered with a different declaration",
                decl.name
            )));
        }

        let mut method_fns = HashMap::with_capacity(decl.methods.len());
        for method in &decl.methods {
            let symbol = trait_method_symbol(&decl.name, &method.name);
            let func_decl = self.declare_trait_method(&symbol, method)?;
            method_fns.insert(method.name.clone(), func_decl);
        }

        let mut default_bodies = HashMap::new();
        for method in &decl.methods {
            if let Some(ref body_text) = method.default_body {
                default_bodies.insert(method.name.clone(), body_text.clone());
            }
        }

        let encoding = TraitEncoding {
            name: decl.name.clone(),
            method_fns,
            default_bodies,
            methods: decl.methods.clone(),
            generics: decl.generics.clone(),
        };

        for method in &decl.methods {
            self.assert_trait_postconditions(decl, method, &encoding)?;
        }

        self.registries
            .trait_encodings
            .insert(decl.name.clone(), encoding.clone());
        Ok(encoding)
    }

    /// Emits per-impl linking axioms for a `TraitImplDecl`.
    ///
    /// For each method binding `(trait_method, concrete_fn)`:
    /// ```text
    /// ∀args. {Trait__method(Box_T(self), ...)}
    ///   Trait__method(Box_T(self), ...) == [Box_T(]concrete_fn(self, ...)[)]
    /// ```
    ///
    /// Requires: trait already registered via `register_trait`.
    /// Requires: concrete impl functions already registered via
    ///           `register_function_context`.
    pub(crate) fn register_trait_impl(&mut self, impl_decl: &TraitImplDecl) -> TrustVcResult<()> {
        let encoding = self
            .registries
            .trait_encodings
            .get(&impl_decl.trait_name)
            .ok_or_else(|| {
                trait_encoding_error(format!(
                    "Cannot register impl for unregistered trait '{}'",
                    impl_decl.trait_name
                ))
            })?
            .clone();

        let (box_fn, _unbox_fn) = self
            .registries
            .poly_context
            .ensure_box_unbox(&mut self.solver, &impl_decl.concrete_type)?;

        // Expose the `Box_T` bridge under its name so caller-side expression
        // encoding (`encode_fn_call`) can resolve the explicit box wrapper that
        // concrete-receiver trait-method calls emit (`Trait__method(Box_S(s),…)`,
        // Slice 1 of #33). Without this the box call is an "Undefined function"
        // (box decls live in `PolyContext`, not `fn_ctx.functions`). Inserting
        // the SAME cached `FuncDecl` keeps the caller's box symbol identical to
        // the one this impl's linking axiom triggers on.
        self.fn_ctx
            .functions
            .entry(box_fn.name().to_string())
            .or_insert_with(|| box_fn.clone());

        for (trait_method_name, concrete_fn_name) in &impl_decl.method_bindings {
            // SOUNDNESS GATE — the shared concrete symbol is not an identity.
            // `concrete_fn_name` is `format!("{type}__{method}")`: it carries the
            // self type but NOT the trait, so an inherent `impl T { fn w }` and
            // this `impl B1 for T { fn w }` mint the SAME string. The axiom
            // emitted below is `B1__w(Box_T(t)) == T__w(t)`, which would equate
            // the trait UF with a symbol the inherent method also defines. Two
            // ways that goes wrong, both measured:
            //   * with the inherent body axiom `T__w(t) == 4` in scope and the
            //     trait postcondition axiom `B1__w(_) == 9`, this axiom asserts
            //     `4 == 9` — a contradiction, which proves everything;
            //   * with the inherent body axiom suppressed instead, the trait's
            //     `ensures` becomes the value of the INHERENT call `t.w()` —
            //     `ensures(result == 9)` VERIFIED while the true `result == 4`
            //     was refuted, against a ground truth of 4 under stock rustc.
            // Rust resolves `t.w()` to the inherent method, so the trait must
            // simply not claim the symbol. The trait's own contract is
            // unaffected: `B1__w` still carries it for the UFCS spellings
            // `B1::w(&t)` / `<T as B1>::w(&t)`, which render trait-qualified and
            // never touch `T__w`.
            if !impl_decl.may_claim_concrete_symbol(trait_method_name) {
                continue;
            }
            // A parameterized signature (bare-TypeParam slots) links only when
            // the impl's trait type args instantiate it soundly; every other
            // TypeParam-bearing shape (blanket impl, nested position, unbound
            // param, requires-bearing) is skipped PER-METHOD, fail-closed.
            // Before this gate, such signatures reached term construction with
            // a Poly-sorted bound var applied to a concrete fn — the resulting
            // Err sank the WHOLE file (`setup.rs` propagates registration
            // errors), rejecting every unrelated function alongside.
            let method_decl = encoding
                .methods
                .iter()
                .find(|method| method.name == *trait_method_name);
            // A method whose return the shared per-trait UF cannot carry gets NO
            // linking axiom — it is resolved instead through the impl method's own
            // definitional body axiom (the with-`self` non-primitive/assoc-return
            // branch of `apply_inherent_impl_methods`). Two shapes:
            //   * `-> Self::Out` (assoc-type projection the impl binds concretely):
            //     the UF keeps the DECLARED abstract sort → "sort mismatch in eq".
            //   * `-> Self` (a `Poly` return): boxing the Poly result into the
            //     concrete fn's sort fails "Box wrapping of result ... got Poly".
            // Both would, being non-generic, sink the whole file. Skip per-method,
            // fail-safe — mirrors the value-side guard in
            // `instantiate_trait_method_sig`. (A `-> W` struct return is a bare
            // `TypeParam` and is already skipped via `declared_generic` below.)
            if method_decl.is_some_and(|method| {
                impl_decl.resolve_assoc_projections(&method.return_type) != method.return_type
                    || matches!(method.return_type, crate::ir::TrustVcType::Poly)
            }) {
                continue;
            }
            let declared_generic = method_decl.is_some_and(|method| {
                method.return_type.contains_type_param()
                    || method
                        .params
                        .iter()
                        .any(|(_, param_ty)| param_ty.contains_type_param())
            });
            let inst_sig = if declared_generic {
                match method_decl.and_then(|method| {
                    crate::trait_instantiation::instantiate_trait_method_sig(
                        &encoding.generics,
                        impl_decl,
                        method,
                    )
                }) {
                    Some(sig) => Some(sig),
                    None => continue,
                }
            } else {
                None
            };

            let result = self.emit_impl_linking_axiom(
                impl_decl,
                trait_method_name,
                concrete_fn_name,
                inst_sig.as_ref(),
                &box_fn,
            );
            if let Err(err) = result {
                if declared_generic {
                    // Bridged path: an unexpected divergence between the impl
                    // signature and the instantiated trait signature must not
                    // re-open the file-sink — the method simply stays without
                    // a linking axiom (callers get no value; fail-closed).
                    continue;
                }
                return Err(err);
            }
        }

        // For default methods not overridden by this impl, emit a per-impl
        // body axiom that defines the trait method UF in terms of the default
        // body expression. Part of #2442.
        let overridden: std::collections::HashSet<&str> = impl_decl
            .method_bindings
            .iter()
            .map(|(name, _)| name.as_str())
            .collect();

        for (method_name, body_text) in &encoding.default_bodies {
            if overridden.contains(method_name.as_str()) {
                continue;
            }
            let method = encoding
                .methods
                .iter()
                .find(|m| m.name == *method_name)
                .ok_or_else(|| {
                    trait_encoding_error(format!(
                        "Default method '{}' not found in trait '{}'",
                        method_name, impl_decl.trait_name
                    ))
                })?;

            // A default body over a TypeParam-bearing signature would define
            // the UF at Poly-erased slots without an instantiation-aware
            // conformance check — skip fail-closed (defensive; the parser does
            // not currently produce such defaults on registrable paths).
            if method.return_type.contains_type_param()
                || method
                    .params
                    .iter()
                    .any(|(_, param_ty)| param_ty.contains_type_param())
            {
                continue;
            }

            // CONTRACT WINS (2026-09-11): a default method that carries an
            // explicit contract publishes ONLY that contract to callers (the
            // postcondition axiom asserted by `assert_trait_postconditions`);
            // its body is checked AGAINST the contract by the conformance lane
            // and is never published as a second, definitional axiom. The two
            // disagree exactly when the conformance obligation is refuted, and
            // publishing both made every function in the file vacuous
            // (measured: "Assumptions are contradictory" for an unrelated
            // `fn a() -> u8 { 20u8 }` beside a `ensures(result == true)`
            // default returning `false` — the whole returns_postcondition port
            // was unverifiable). A contract-free default keeps its body axiom:
            // there the body IS the only spec, as before.
            if !method.ensures.is_empty() || !method.default_ensures.is_empty() {
                continue;
            }

            // A default body whose SHAPE the axiom fragment cannot express —
            // proof-macro statements (`trust_vc::assert!` is "macro in block"
            // to the spec lowering) or constructs the minimal trait-contract
            // env has no metadata for (a user struct literal) — used to sink
            // the WHOLE file: `setup.rs` propagates registration errors, so
            // every unrelated function in the file was rejected alongside
            // (the same file-sink pattern the A2-generic gate closed for
            // generic signatures). Skip THIS method's definitional axiom
            // instead, fail-closed: the trait UF stays underconstrained, so
            // callers get NO value from the default body — omitting an
            // assumption can only shrink provability, never manufacture a
            // false-Verified. Parse/lowering errors are exactly the
            // deterministic shape-unsupported class; encoding/solver failures
            // still propagate and fail the file, per the fail-closed
            // discipline (design-unknown-as-failure.md).
            if let Err(err) =
                self.assert_default_body_axiom(&encoding, impl_decl, method, body_text)
            {
                match err {
                    TrustVcError::Parse {
                        context: "parse default body",
                        ..
                    }
                    | TrustVcError::Lowering {
                        context: "lower default body",
                        ..
                    } => continue,
                    other => return Err(other),
                }
            }
        }

        Ok(())
    }

    /// Builds and asserts ONE per-impl linking axiom
    /// `∀(self:T, vars). {Trait__m(Box_T(self), …)} Trait__m(Box_T(self), …) == concrete_fn(self, …)`.
    ///
    /// `inst_sig` is `Some` exactly for a parameterized-trait method whose
    /// signature the impl's trait type args instantiate (trait-side
    /// A2-generic): each bare-TypeParam position binds a CONCRETE-sorted
    /// variable that crosses a `Box_{inst}` bridge on the UF side and passes
    /// raw to the concrete fn; a bridged return wraps the concrete result in
    /// `Box_{inst}`. The boxed receiver and the bridge terms are part of the
    /// axiom itself, not only of its trigger, so the axiom states nothing
    /// about a receiver or an argument of another type: that is what keeps
    /// distinct instantiations and impls apart.
    fn emit_impl_linking_axiom(
        &mut self,
        impl_decl: &TraitImplDecl,
        trait_method_name: &str,
        concrete_fn_name: &str,
        inst_sig: Option<&crate::trait_instantiation::InstantiatedTraitMethodSig>,
        box_fn: &FuncDecl,
    ) -> TrustVcResult<()> {
        let trait_method_fn = self
            .registries
            .trait_encodings
            .get(&impl_decl.trait_name)
            .and_then(|encoding| encoding.method_fns.get(trait_method_name))
            .cloned()
            .ok_or_else(|| {
                trait_encoding_error(format!(
                    "Trait '{}' has no method '{}' (impl for {})",
                    impl_decl.trait_name,
                    trait_method_name,
                    impl_decl.concrete_type.to_type_string()
                ))
            })?;

        let concrete_fn = self
            .fn_ctx
            .functions
            .get(concrete_fn_name)
            .cloned()
            .ok_or_else(|| {
                trait_encoding_error(format!(
                    "Concrete function '{}' not registered (impl {}::{})",
                    concrete_fn_name, impl_decl.trait_name, trait_method_name
                ))
            })?;

        // Look up the trait method's parameter types (Poly self + extra params)
        let trait_uf_name = trait_method_symbol(&impl_decl.trait_name, trait_method_name);
        let trait_method_params = self
            .fn_ctx
            .param_types
            .get(&trait_uf_name)
            .ok_or_else(|| {
                trait_encoding_error(format!(
                    "Missing param types for trait method '{trait_uf_name}'"
                ))
            })?
            .clone();

        let trait_method_return_type = self
            .fn_ctx
            .return_types
            .get(&trait_uf_name)
            .ok_or_else(|| {
                trait_encoding_error(format!(
                    "Missing return type for trait method '{trait_uf_name}'"
                ))
            })?
            .clone();

        // `self` ranges over the impl's OWN type and reaches the trait UF as
        // `Box_T(self)`, so the axiom speaks only of receivers that are boxed
        // `T` values. A `Poly` receiver unboxed with `Unbox_T` on the concrete
        // side would instead claim that EVERY receiver, a second impl's and a
        // generic caller's included, dispatches to this impl. That claim is
        // false as soon as another impl behaves differently, and a solver that
        // adopts the axiom as a definition of the trait UF uses it: two unit
        // struct impls with different postconditions then prove `false`, and a
        // caller comparing the two impls' results verifies a false equality.
        let self_var = self.solver.fresh_var(
            &format!(
                "__impl_{}_{}_self",
                sanitize_symbol(&impl_decl.trait_name),
                sanitize_symbol(trait_method_name)
            ),
            sort_for_type(&impl_decl.concrete_type),
        );
        let boxed_self = self
            .solver
            .try_apply(box_fn, &[self_var])
            .map_err(|e| trait_encoding_error(format!("Box application failed: {e}")))?;

        let mut bound_vars = vec![self_var];
        // UF-side (possibly Box-bridged) and concrete-fn-side (always raw)
        // argument terms, aligned per non-self position.
        let mut trait_side_args = Vec::new();
        let mut concrete_side_args = Vec::new();

        // trait_method_params[0] is Poly (self), rest are extra params
        for (i, param_ty) in trait_method_params.iter().skip(1).enumerate() {
            let bridge = inst_sig
                .and_then(|sig| sig.params.get(i))
                .and_then(|(_, bridge)| bridge.clone());
            if let Some(inst_ty) = bridge {
                // Bridged position: the UF slot is Poly-sorted, the value is
                // concrete. Quantify over the CONCRETE sort and box it on the
                // UF side only — the caller's ground term carries the same
                // `Box_{inst}(arg)` shape (the #2053 call-site bridging), so
                // the trigger unifies exactly per instantiation.
                let param_var = self.solver.fresh_var(
                    &format!(
                        "__impl_{}_{}_{i}",
                        sanitize_symbol(&impl_decl.trait_name),
                        sanitize_symbol(trait_method_name),
                    ),
                    sort_for_type(&inst_ty),
                );
                let (arg_box_fn, _arg_unbox_fn) = self
                    .registries
                    .poly_context
                    .ensure_box_unbox(&mut self.solver, &inst_ty)?;
                let boxed = self
                    .solver
                    .try_apply(&arg_box_fn, &[param_var])
                    .map_err(|e| {
                        trait_encoding_error(format!("Bridged param boxing failed: {e}"))
                    })?;
                bound_vars.push(param_var);
                trait_side_args.push(boxed);
                concrete_side_args.push(param_var);
            } else {
                let param_var = self.solver.fresh_var(
                    &format!(
                        "__impl_{}_{}_{i}",
                        sanitize_symbol(&impl_decl.trait_name),
                        sanitize_symbol(trait_method_name),
                    ),
                    sort_for_type(param_ty),
                );
                bound_vars.push(param_var);
                trait_side_args.push(param_var);
                concrete_side_args.push(param_var);
            }
        }

        // LHS: Trait__method(Box_T(self), trait_side_args...)
        let mut trait_args = vec![boxed_self];
        trait_args.extend(trait_side_args.iter().copied());

        let lhs = self
            .solver
            .try_apply(&trait_method_fn, &trait_args)
            .map_err(|e| trait_encoding_error(format!("Trait method application failed: {e}")))?;

        // RHS: concrete_fn(self, concrete_side_args...)
        let mut concrete_args = vec![self_var];
        concrete_args.extend(concrete_side_args.iter().copied());

        let concrete_result = self
            .solver
            .try_apply(&concrete_fn, &concrete_args)
            .map_err(|e| {
                trait_encoding_error(format!("Concrete function application failed: {e}"))
            })?;

        // A Poly (Self) return wraps with the impl's own Box_T; a bridged
        // TypeParam return wraps with the instantiation's Box_{inst} so the
        // equality stays Poly-sorted against the UF.
        let rhs = if trait_method_return_type == TrustVcType::Poly {
            self.solver
                .try_apply(box_fn, &[concrete_result])
                .map_err(|e| trait_encoding_error(format!("Box wrapping of result failed: {e}")))?
        } else if let Some(inst_ty) = inst_sig.and_then(|sig| sig.return_bridge.clone()) {
            let (ret_box_fn, _ret_unbox_fn) = self
                .registries
                .poly_context
                .ensure_box_unbox(&mut self.solver, &inst_ty)?;
            self.solver
                .try_apply(&ret_box_fn, &[concrete_result])
                .map_err(|e| trait_encoding_error(format!("Bridged result boxing failed: {e}")))?
        } else {
            concrete_result
        };

        // Assert: ∀(self:T, params). {Trait__method(Box_T(self), ...)} lhs == rhs
        let eq = self
            .solver
            .try_eq(lhs, rhs)
            .map_err(|e| trait_encoding_error(format!("Equality failed: {e}")))?;

        let axiom = self
            .solver
            .try_forall_with_triggers(&bound_vars, eq, &[&[lhs]])
            .map_err(|e| {
                trait_encoding_error(format!(
                    "Quantified linking axiom failed for '{}::{}': {e}",
                    impl_decl.trait_name, trait_method_name
                ))
            })?;

        self.solver.try_assert_term(axiom).map_err(|e| {
            trait_encoding_error(format!(
                "Failed to assert linking axiom for '{}::{}': {e}",
                impl_decl.trait_name, trait_method_name
            ))
        })?;
        Ok(())
    }
}
