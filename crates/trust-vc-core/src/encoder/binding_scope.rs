//! Local binding scope helpers for save/restore of `local_vars` and `local_var_types`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Centralizes the pattern of saving an existing local binding before shadowing
//! it with a new term/type, and restoring the old binding afterward. Previously
//! this was duplicated across quantifier, match, let, choose, and collection
//! higher-order encoder paths. Consolidation: #2609.
//!
//! Three layers:
//! - `save_local_binding` — single-variable save + overwrite
//! - `restore_locals` — batch restore from saved bindings
//! - `with_local_bindings` — closure-based convenience (guarantees restore on error)

use ay_dpll::api::Term;

use crate::ir::TrustVcType;

use super::AstExpressionParser;

/// A saved local binding: (name, old term, old type).
pub(in crate::encoder) type SavedLocalBinding = (String, Option<Term>, Option<TrustVcType>);

impl<'a> AstExpressionParser<'a> {
    /// Save the current local binding for `name`, then overwrite both maps
    /// with `term` and `ty`. Returns the saved state for later restore.
    pub(in crate::encoder) fn save_local_binding(
        &mut self,
        name: impl Into<String>,
        term: Term,
        ty: TrustVcType,
    ) -> SavedLocalBinding {
        let name = name.into();
        let old_var = self.local_vars.insert(name.clone(), term);
        let old_ty = self.local_var_types.insert(name.clone(), ty);
        (name, old_var, old_ty)
    }

    /// Restore saved local variable bindings after scope exit.
    ///
    /// For each saved entry, restores the old value if present, or removes
    /// the key if there was no prior binding (the variable was introduced,
    /// not shadowed).
    pub(in crate::encoder) fn restore_locals(&mut self, saved: Vec<SavedLocalBinding>) {
        for (name, old_var, old_ty) in saved {
            match old_var {
                Some(v) => {
                    self.local_vars.insert(name.clone(), v);
                }
                None => {
                    self.local_vars.remove(&name);
                }
            }
            match old_ty {
                Some(t) => {
                    self.local_var_types.insert(name, t);
                }
                None => {
                    self.local_var_types.remove(&name);
                }
            }
        }
    }

    /// Execute `f` with temporary local bindings, restoring the old state
    /// afterward — even if `f` returns `Err`.
    ///
    /// Modeled after `encode_with_overflow_guard` (overflow_guard.rs). This
    /// guarantees restore on all exit paths without requiring callers to
    /// manually pair save/restore around fallible operations.
    pub(in crate::encoder) fn with_local_bindings<R>(
        &mut self,
        bindings: impl IntoIterator<Item = (String, Term, TrustVcType)>,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let saved: Vec<SavedLocalBinding> = bindings
            .into_iter()
            .map(|(name, term, ty)| self.save_local_binding(name, term, ty))
            .collect();
        let result = f(self);
        self.restore_locals(saved);
        result
    }

    /// Encode a SPEC-closure / predicate body (`Seq`/`Set`/`Map`
    /// `map`/`filter`/`fold`/…) with temporary local bindings, while suppressing
    /// the auto-emitted fixed-width arithmetic-safety obligations (overflow /
    /// divide-by-zero / shift-bounds) that the body would otherwise leak into the
    /// enclosing scope.
    ///
    /// Comprehension and higher-order spec operations apply their `SpecFn`
    /// closures to a universally-bound element/index that ranges over the whole
    /// (unbounded) domain. In Verus these closures are SPEC mode, where
    /// arithmetic is mathematical `int`/`nat` and is **never** overflow-checked —
    /// so encoding e.g. `2 * i` on a fixed-width (`usize`/`i32`) bound variable
    /// must not collect a per-operation bit-vector overflow obligation. Emitting
    /// one yields a *false counterexample*: the obligation refutes on the
    /// unconstrained bound variable (`2 * usize::MAX` overflows) even when the
    /// surrounding goal (`s.map(f).len() == s.len()`) is trivially true and the
    /// closure is never evaluated on a real element (e.g. an empty sequence).
    ///
    /// The overflow / div0 / shift side checks in `encode_arith` /
    /// `encode_int_arith` / `encode_special_arith` / negation are each gated on
    /// the corresponding `*_behavior.should_check()`. This helper temporarily
    /// drops those behaviors around the body encoding:
    ///   * `overflow_behavior` → `Truncate`, NOT `Allow`: `Truncate` keeps
    ///     `should_clip()` true, so the body's *value* term (BV wrap / int clip)
    ///     is encoded byte-identically to the exec path — only the `should_check()`
    ///     obligation collection is dropped. (`Allow` would additionally disable
    ///     clipping and thus change the encoded value.)
    ///   * `div0_behavior`/`bitshift_behavior` → `Allow`: these only gate the
    ///     non-zero-divisor / in-range-shift obligations; the div/rem/shift result
    ///     terms are computed regardless, so the value encoding is unchanged.
    ///
    /// Crucially this does NOT touch `quantifier_depth`, so the body's term,
    /// trigger shape, and every other depth-gated decision (e.g. concrete-index
    /// e-matching for `s.map(f).index(k)`) stay exactly as in the current
    /// encoding — only the spurious spec-closure safety obligations disappear.
    /// Genuine EXEC arithmetic is always encoded at depth 0 in a function body
    /// (never inside a comprehension closure) with the real exec behaviors, so its
    /// overflow obligations are preserved exactly.
    pub(in crate::encoder) fn with_closure_body_bindings<R>(
        &mut self,
        bindings: impl IntoIterator<Item = (String, Term, TrustVcType)>,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let saved_overflow = self.overflow_behavior;
        let saved_div0 = self.div0_behavior;
        let saved_bitshift = self.bitshift_behavior;
        // Drop only the obligation collection, never the value encoding:
        // `Truncate` preserves clipping (`should_clip()`), `Allow` div0/shift
        // only drop their non-value checks.
        self.overflow_behavior = crate::vc::OverflowBehavior::Truncate;
        self.div0_behavior = crate::vc::Div0Behavior::Allow;
        self.bitshift_behavior = crate::vc::BitshiftBehavior::Allow;
        let result = self.with_local_bindings(bindings, f);
        self.overflow_behavior = saved_overflow;
        self.div0_behavior = saved_div0;
        self.bitshift_behavior = saved_bitshift;
        result
    }
}
