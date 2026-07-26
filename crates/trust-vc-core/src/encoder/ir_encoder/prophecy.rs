//! Prophecy variable encoding — Part of #2519.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Encodes `ProphecyNew` as a fresh unconstrained ay constant and
//! `ProphecyResolve` as an equality assertion constraining the prophecy
//! to a concrete value. Follows the choose.rs registry pattern.

use ay_dpll::api::Term;

use crate::encoder::types::sort_for_type;
use crate::error::TrustVcResult;
use crate::ir::TrustVcType;

use crate::encoder::AstExpressionParser;

impl<'a> AstExpressionParser<'a> {
    /// Encode `ProphecyNew { name, ty }` as a fresh unconstrained constant.
    ///
    /// The prophecy term is registered so that subsequent `ProphecyResolve`
    /// with the same name can look it up and constrain it.
    pub(super) fn encode_prophecy_new(
        &mut self,
        name: &str,
        ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let registry = self.prophecy_registry.as_mut().ok_or_else(|| {
            "prophecy: no prophecy_registry available (internal error)".to_string()
        })?;

        if let Some(existing) = registry.get(name) {
            return Ok(*existing);
        }

        let sort = sort_for_type(ty);
        let term = self
            .solver
            .fresh_var(&format!("__trust_vc_prophecy_{}", registry.len()), sort);

        registry.insert(name.to_string(), term);

        // Track width metadata for downstream coercion.
        if let Some(width) = ty.bit_width() {
            if width > 0 {
                let signed = matches!(ty, TrustVcType::Int { .. });
                self.term_widths.insert(term, (width, signed));
            }
        }

        if matches!(ty, TrustVcType::Unit) {
            super::super::unit::assert_unit_term(self.solver, term, "encode prophecy", name)?;
        }

        Ok(term)
    }

    /// Encode `ProphecyResolve { name, value }` as an equality assertion.
    ///
    /// Constrains the previously-unconstrained prophecy constant to equal
    /// the resolved value, retroactively making all prior reasoning about
    /// the prophecy consistent with the resolved value.
    pub(super) fn encode_prophecy_resolve(
        &mut self,
        name: &str,
        value: &crate::ir::TrustVcExpr,
    ) -> TrustVcResult<Term> {
        let prophecy_term = self
            .prophecy_registry
            .as_ref()
            .and_then(|r| r.get(name).copied())
            .ok_or_else(|| format!("prophecy: unresolved prophecy '{}'", name))?;

        let value_term = self.encode_subexpr(value)?;

        let eq = self
            .solver
            .try_eq(prophecy_term, value_term)
            .map_err(|e| format!("prophecy resolve: {}", e))?;

        self.solver
            .try_assert_term(eq)
            .map_err(|e| format!("prophecy resolve assert: {}", e))?;

        Ok(prophecy_term)
    }
}
