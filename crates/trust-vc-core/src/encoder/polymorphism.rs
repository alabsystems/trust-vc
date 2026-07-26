//! Poly/Box/Unbox type-erasure encoding for polymorphic functions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Implements Verus-style type erasure: a single uninterpreted sort `Poly`
//! represents all type-erased values. For each concrete type T used at a
//! generic call site:
//! - `Box_T: T_sort → Poly` wraps a concrete value into the universal sort
//! - `Unbox_T: Poly → T_sort` projects back to the concrete sort
//!
//! The encoder asserts ground roundtrip facts at concrete call sites:
//! `Unbox_T(Box_T(v)) == v`. This avoids leaving live Poly quantifiers in SAT
//! queries, where ay-dpll may otherwise report `QuantifierUnhandled`.
//!
//! Part of #2053 (polymorphism encoding).
use std::collections::HashMap;

use ay_dpll::api::{FuncDecl, Solver, Sort};

use crate::encoder::types::sort_for_type;
use crate::encoder::AYEncoder;
use crate::error::TrustVcResult;
use crate::ir::TrustVcType;

/// Tracks Box/Unbox function declarations for concrete types.
pub(crate) struct PolyContext {
    /// Box_T declarations keyed by type string.
    box_fns: HashMap<String, FuncDecl>,
    /// Unbox_T declarations keyed by type string.
    unbox_fns: HashMap<String, FuncDecl>,
    /// True once a Box/Unbox bridge has been declared for a concrete
    /// `TrustVcType::Datatype` carrier — i.e. a type-erased value of a struct/enum
    /// type was bridged through `Poly`. Scopes the under-constrained-model
    /// incompleteness guard (`verify_assertion_typed`) to the datatype
    /// field-projection shape, where the `Unbox_T(Poly) -> Datatype` projection is
    /// fully uninterpreted and a SAT model can leave the projected field
    /// unconstrained. Scalar bridges (BV/Bool — e.g. `identity::<u64>(5) == 6`,
    /// `hidden::<bool>(t, 4) == 5`) decide such goals through a real theory, so
    /// their model-less counterexamples stay genuine refutations. Part of #2778.
    datatype_bridge_declared: bool,
}

impl PolyContext {
    pub(crate) fn new() -> Self {
        Self {
            box_fns: HashMap::new(),
            unbox_fns: HashMap::new(),
            datatype_bridge_declared: false,
        }
    }

    /// Ensures Box_T and Unbox_T are declared for a concrete type.
    /// Idempotent — skips if already declared.
    ///
    /// Returns cloned (Box_T, Unbox_T) function declarations.
    pub(crate) fn ensure_box_unbox(
        &mut self,
        solver: &mut Solver,
        concrete_type: &TrustVcType,
    ) -> TrustVcResult<(FuncDecl, FuncDecl)> {
        let type_key = concrete_type.to_type_string();
        if matches!(concrete_type, TrustVcType::Datatype { .. }) {
            self.datatype_bridge_declared = true;
        }
        if let (Some(box_fn), Some(unbox_fn)) =
            (self.box_fns.get(&type_key), self.unbox_fns.get(&type_key))
        {
            return Ok((box_fn.clone(), unbox_fn.clone()));
        }

        let concrete_sort = sort_for_type(concrete_type);
        let poly_sort = Sort::Uninterpreted("Poly".to_string());

        let box_name = format!("Box_{}", type_key);
        let unbox_name = format!("Unbox_{}", type_key);

        let box_fn = solver
            .try_declare_fun(
                &box_name,
                std::slice::from_ref(&concrete_sort),
                poly_sort.clone(),
            )
            .map_err(|e| crate::error::TrustVcError::from(e.to_string()))?;
        let unbox_fn = solver
            .try_declare_fun(&unbox_name, &[poly_sort], concrete_sort.clone())
            .map_err(|e| crate::error::TrustVcError::from(e.to_string()))?;

        self.box_fns.insert(type_key.clone(), box_fn.clone());
        self.unbox_fns.insert(type_key, unbox_fn.clone());

        Ok((box_fn, unbox_fn))
    }

    /// True iff a Box/Unbox bridge has been declared for a concrete
    /// `TrustVcType::Datatype` carrier in this query — i.e. a struct/enum value was
    /// type-erased through `Poly`.
    ///
    /// Scopes the under-constrained-model incompleteness guard
    /// (`verify_assertion_typed`) to the generic-DATATYPE field-projection shape:
    /// the `Unbox_T(Poly) -> Datatype` projection is fully uninterpreted, so when
    /// ay's ground instantiation fails to fire the definitional body axiom the SAT
    /// model leaves the projected field unconstrained (no concrete witness). Scalar
    /// bridges (BV/Bool) decide their goals through a real theory, so their
    /// model-less counterexamples are genuine refutations and stay counterexamples.
    /// Part of #2778.
    pub(crate) fn has_datatype_bridge(&self) -> bool {
        self.datatype_bridge_declared
    }

    /// Returns the Box_T declaration for a type, if previously declared.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn get_box_fn(&self, concrete_type: &TrustVcType) -> Option<&FuncDecl> {
        self.box_fns.get(&concrete_type.to_type_string())
    }

    /// Returns the Unbox_T declaration for a type, if previously declared.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn get_unbox_fn(&self, concrete_type: &TrustVcType) -> Option<&FuncDecl> {
        self.unbox_fns.get(&concrete_type.to_type_string())
    }
}

impl AYEncoder {
    /// Returns the cached Box_T declaration for a concrete type, if present.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn box_fn_for_type(&self, concrete_type: &TrustVcType) -> Option<&FuncDecl> {
        self.registries.poly_context.get_box_fn(concrete_type)
    }
}
