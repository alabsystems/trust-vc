//! Shared eligibility + instantiation for parameterized-trait method
//! signatures (trait-side A2-generic).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! ONE predicate consumed in lockstep by the encoder (instantiated Box-bridged
//! linking axiom, `encoder/trait_encoding.rs`) and the TypeEnv gate
//! (instantiated `MethodMeta`, `prepared_context/type_env.rs`): an axiom is
//! never emitted for a term shape callers cannot form, and no caller-side
//! registration exists without its matching axiom. Everything outside the
//! instantiable set returns `None` and every consumer must skip fail-closed
//! (no axiom, no `MethodMeta`, no error, file not sunk).

use crate::ir::{TraitImplDecl, TraitMethodDecl, TrustVcType};

/// A trait method signature instantiated at a concrete trait-type-arg binding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InstantiatedTraitMethodSig {
    /// Per non-self param: the instantiated type, plus `Some(concrete)` iff
    /// the DECLARED position was a bare `TypeParam` — i.e. the trait UF slot
    /// is Poly-sorted and the value must cross a `Box_{concrete}` bridge.
    pub(crate) params: Vec<(TrustVcType, Option<TrustVcType>)>,
    pub(crate) return_type: TrustVcType,
    /// `Some(concrete)` iff the declared return was a bare `TypeParam`.
    pub(crate) return_bridge: Option<TrustVcType>,
}

impl InstantiatedTraitMethodSig {
    /// True iff any position actually crosses a Box/Unbox bridge (i.e. the
    /// method genuinely engages the trait's generics).
    pub(crate) fn has_bridge(&self) -> bool {
        self.return_bridge.is_some() || self.params.iter().any(|(_, bridge)| bridge.is_some())
    }
}

/// True iff `ty` is fully concrete: not `Poly`, no `TypeParam`, no opaque
/// component — the same bar `is_concrete_boxable_type` applies on the TypeEnv
/// side.
pub(crate) fn is_fully_concrete(ty: &TrustVcType) -> bool {
    !matches!(ty, TrustVcType::Poly) && !ty.contains_type_param() && !ty.contains_opaque()
}

/// Instantiates `method`'s signature under `impl_decl`'s trait type args, or
/// returns `None` (fail closed) when the method is not instantiable.
///
/// Eligibility (every consumer relies on ALL of these):
/// * a position whose declared type contains no `TypeParam` passes through
///   UNCHANGED (bridge `None`) — non-generic signatures keep today's behavior
///   byte-for-byte, including under a parameterized trait;
/// * a position that is EXACTLY a bare `TypeParam(Ai)` is bound positionally
///   via `zip(trait_generics, trait_type_args)`; the binding must exist and be
///   fully concrete. Its trait-UF slot is Poly-sorted, so the value crosses a
///   `Box_{binding}` bridge;
/// * any OTHER `TypeParam` occurrence (nested: `Seq<A>`, tuples, datatype
///   fields) → `None`: the erased slot is a container-of-Poly, not fixable by
///   a top-level Box;
/// * a position that `resolve_assoc_projections` would REWRITE (`Self::X`
///   with an impl binding) → `None`: the per-trait UF is declared ONCE from
///   DECLARED types (`Opaque("Self::X")` → `Sort::Int`), so an impl-resolved
///   concrete type would sort-diverge from that shared slot. A3 resolves
///   associated-type projections structurally at the TARGET-LIFTING seam
///   (`AssocProjectionResolver`), where the concrete type lands in a fresh
///   variable's OWN sort — but a BRIDGED trait-method position lowers into the
///   shared per-trait UF slot, whose sort cannot be reconciled per-impl without
///   monomorphizing the UF per impl. That reconciliation is out of scope, so
///   this position stays fail-closed (a false-verify is never worth the reach);
/// * a method that engages a bridge must be `requires`-free: the caller-side
///   requires-discharge map skips generic impls, so callers must never
///   consume a contract whose requires nothing discharges.
pub(crate) fn instantiate_trait_method_sig(
    trait_generics: &[String],
    impl_decl: &TraitImplDecl,
    method: &TraitMethodDecl,
) -> Option<InstantiatedTraitMethodSig> {
    if trait_generics.len() != impl_decl.trait_type_args.len() {
        return None;
    }

    let instantiate_position =
        |declared: &TrustVcType| -> Option<(TrustVcType, Option<TrustVcType>)> {
            // A position an impl assoc-type binding would rewrite stays fail-closed:
            // the per-trait UF slot keeps the DECLARED sort, which an impl-resolved
            // type would no longer match. A3 resolves projections that land in a
            // fresh variable's own sort (the target-lifting seam), NOT this shared
            // per-trait UF slot, so lifting this guard would still sort-diverge.
            if impl_decl.resolve_assoc_projections(declared) != *declared {
                return None;
            }
            match declared {
                TrustVcType::TypeParam(name) => {
                    let (_, binding) = trait_generics
                        .iter()
                        .zip(impl_decl.trait_type_args.iter())
                        .find(|(generic, _)| *generic == name)?;
                    if !is_fully_concrete(binding) {
                        return None;
                    }
                    Some((binding.clone(), Some(binding.clone())))
                }
                ty if ty.contains_type_param() => None,
                ty => Some((ty.clone(), None)),
            }
        };

    let mut params = Vec::with_capacity(method.params.len());
    for (_, declared) in &method.params {
        params.push(instantiate_position(declared)?);
    }
    let (return_type, return_bridge) = instantiate_position(&method.return_type)?;

    let sig = InstantiatedTraitMethodSig {
        params,
        return_type,
        return_bridge,
    };

    if sig.has_bridge() {
        if !method.requires.is_empty() {
            return None;
        }
        // Residual backstop (twin of the inherent-path `contains_type_param`
        // guards): every bridged position must have landed fully concrete.
        let bridged_concrete = sig
            .params
            .iter()
            .map(|(ty, _)| ty)
            .chain(std::iter::once(&sig.return_type))
            .all(|ty| matches!(ty, TrustVcType::Poly) || is_fully_concrete(ty));
        if !bridged_concrete {
            return None;
        }
    }

    Some(sig)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::TraitImplDecl;

    fn method(
        params: Vec<(&str, TrustVcType)>,
        return_type: TrustVcType,
        requires: Vec<&str>,
    ) -> TraitMethodDecl {
        TraitMethodDecl {
            name: "m".to_string(),
            params: params
                .into_iter()
                .map(|(name, ty)| (name.to_string(), ty))
                .collect(),
            return_type,
            requires: requires.into_iter().map(str::to_string).collect(),
            ensures: vec!["true".to_string()],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
        }
    }

    fn impl_at(args: Vec<TrustVcType>) -> TraitImplDecl {
        TraitImplDecl::new("T", TrustVcType::Opaque("S".to_string()), Vec::new())
            .with_trait_type_args(args)
    }

    fn u64_ty() -> TrustVcType {
        TrustVcType::Uint { width: 64 }
    }

    fn tp(name: &str) -> TrustVcType {
        TrustVcType::TypeParam(name.to_string())
    }

    #[test]
    fn bare_type_param_bridges_to_binding() {
        let sig = instantiate_trait_method_sig(
            &["A".to_string()],
            &impl_at(vec![u64_ty()]),
            &method(vec![("a", tp("A"))], tp("A"), vec![]),
        )
        .expect("bare TypeParam positions instantiate");
        assert_eq!(sig.params, vec![(u64_ty(), Some(u64_ty()))]);
        assert_eq!(sig.return_type, u64_ty());
        assert_eq!(sig.return_bridge, Some(u64_ty()));
        assert!(sig.has_bridge());
    }

    #[test]
    fn non_generic_signature_is_identity_even_under_generic_trait() {
        let sig = instantiate_trait_method_sig(
            &["A".to_string()],
            &impl_at(vec![u64_ty()]),
            &method(vec![("x", TrustVcType::Bool)], TrustVcType::Bool, vec![]),
        )
        .expect("concrete signature passes through");
        assert_eq!(sig.params, vec![(TrustVcType::Bool, None)]);
        assert_eq!(sig.return_bridge, None);
        assert!(!sig.has_bridge());
    }

    #[test]
    fn requires_bearing_concrete_signature_still_identity() {
        // The requires gate applies ONLY to bridged methods; a requires-bearing
        // fully-concrete method must keep today's registration behavior.
        let sig = instantiate_trait_method_sig(
            &[],
            &impl_at(vec![]),
            &method(vec![("x", u64_ty())], TrustVcType::Bool, vec!["x > 0"]),
        );
        assert!(sig.is_some());
    }

    #[test]
    fn requires_bearing_bridged_method_fails_closed() {
        let sig = instantiate_trait_method_sig(
            &["A".to_string()],
            &impl_at(vec![u64_ty()]),
            &method(vec![("a", tp("A"))], tp("A"), vec!["a > 0"]),
        );
        assert!(sig.is_none());
    }

    #[test]
    fn nested_type_param_fails_closed() {
        let sig = instantiate_trait_method_sig(
            &["A".to_string()],
            &impl_at(vec![u64_ty()]),
            &method(
                vec![("xs", TrustVcType::Seq(Box::new(tp("A"))))],
                TrustVcType::Bool,
                vec![],
            ),
        );
        assert!(sig.is_none());
    }

    #[test]
    fn arity_mismatch_fails_closed() {
        let sig = instantiate_trait_method_sig(
            &["A".to_string(), "B".to_string()],
            &impl_at(vec![u64_ty()]),
            &method(vec![("a", tp("A"))], TrustVcType::Bool, vec![]),
        );
        assert!(sig.is_none());
    }

    #[test]
    fn non_concrete_binding_fails_closed() {
        let sig = instantiate_trait_method_sig(
            &["A".to_string()],
            &impl_at(vec![tp("C")]),
            &method(vec![("a", tp("A"))], TrustVcType::Bool, vec![]),
        );
        assert!(sig.is_none());
    }

    #[test]
    fn opaque_binding_fails_closed() {
        let sig = instantiate_trait_method_sig(
            &["A".to_string()],
            &impl_at(vec![TrustVcType::Opaque(
                "<unsupported-trait-generic-arg>".to_string(),
            )]),
            &method(vec![("a", tp("A"))], TrustVcType::Bool, vec![]),
        );
        assert!(sig.is_none());
    }

    #[test]
    fn unbound_type_param_fails_closed() {
        let sig = instantiate_trait_method_sig(
            &["A".to_string()],
            &impl_at(vec![u64_ty()]),
            &method(vec![("b", tp("B"))], TrustVcType::Bool, vec![]),
        );
        assert!(sig.is_none());
    }

    #[test]
    fn assoc_projection_in_bridged_method_stays_fail_closed() {
        // Post-A3 SOUND boundary: A3 resolves associated-type projections at the
        // target-lifting seam, where a resolved concrete type lands in a fresh
        // variable's OWN sort. A BRIDGED trait-method position typed `Self::X`
        // instead lowers into the SHARED per-trait UF slot, declared once from
        // the DECLARED `Opaque("Self::X")` sort; an impl-resolved concrete type
        // would sort-diverge from it. Reconciling that would require
        // monomorphizing the per-trait UF per impl (out of scope), so this
        // position MUST stay fail-closed — never emit a sort-mismatched term.
        let impl_decl = TraitImplDecl::new("T", TrustVcType::Opaque("S".to_string()), Vec::new())
            .with_assoc_type_bindings(vec![("X".to_string(), u64_ty())])
            .with_trait_type_args(vec![u64_ty()]);
        let sig = instantiate_trait_method_sig(
            &["A".to_string()],
            &impl_decl,
            &method(
                vec![("x", TrustVcType::Opaque("Self::X".to_string()))],
                tp("A"),
                vec![],
            ),
        );
        assert!(
            sig.is_none(),
            "impl-resolved Self::X would sort-diverge from the shared per-trait UF slot"
        );
    }

    #[test]
    fn binding_order_is_positional() {
        let sig = instantiate_trait_method_sig(
            &["A".to_string(), "B".to_string()],
            &impl_at(vec![u64_ty(), TrustVcType::Bool]),
            &method(vec![("a", tp("A")), ("b", tp("B"))], tp("B"), vec![]),
        )
        .expect("both params instantiate");
        assert_eq!(
            sig.params,
            vec![
                (u64_ty(), Some(u64_ty())),
                (TrustVcType::Bool, Some(TrustVcType::Bool)),
            ]
        );
        assert_eq!(sig.return_type, TrustVcType::Bool);
    }

    #[test]
    fn poly_self_position_passes_through_unbridged() {
        // A declared-`Poly` (Self-typed) position keeps today's behavior: it
        // passes through and stays rejected by `is_concrete_boxable_type` on
        // the TypeEnv side (deferred, not this increment's concern).
        let sig = instantiate_trait_method_sig(
            &["A".to_string()],
            &impl_at(vec![u64_ty()]),
            &method(vec![("s", TrustVcType::Poly)], tp("A"), vec![]),
        )
        .expect("Poly position passes through for the encoder");
        assert_eq!(sig.params, vec![(TrustVcType::Poly, None)]);
        assert_eq!(sig.return_bridge, Some(u64_ty()));
    }
}
