//! Bare no-op marker shims for the rustc-driver front end (surface bridge).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Under `--cfg trust_vc_driver`, the trust_vc contract macros
//! (`requires!`/`ensures!`/`forall!`/`exists!`) expand to *calls of these
//! functions* instead of a runtime `assert!`, the syn collection path, or a
//! vacuous `true`. The rustc-driver front end (`trust-vc-driver::driver`)
//! recognizes a verification target purely by `callee_name` — i.e. the callee's
//! `item_name` being `requires` / `ensures` / `forall` / `exists` — then walks
//! the fully type-checked THIR and lowers the REAL predicate / quantifier.
//!
//! The proc-macro crate `trust-vc` cannot host these (a `proc-macro = true`
//! crate may only export procedural macros), so they live here in the runtime
//! support crate that every expansion already routes through
//! (`macro_support_root()` → `::trust_vc_core`). The driver matches on
//! `item_name` alone, so the hosting crate/module is irrelevant to recognition.
//!
//! # Soundness (the paramount guard)
//!
//! These BODIES are never the verification meaning. The driver reads the THIR
//! call node and — for the quantifiers — the CLOSURE argument, never the shim
//! body. `forall`/`exists` return `true` *only* so the contract surface
//! type-checks under vanilla rustc; the driver lowers a real `∀`/`∃` from the
//! closure, so a FALSE quantified postcondition (e.g. `forall(|x| x < x)`) is
//! REFUTED, never vacuously verified. Emitting these marker calls — rather than
//! a bare `true` — is exactly what prevents the vacuous-true (false-Verify)
//! leak the driver's `lower_quantifier` was built to reject.

/// `requires!(b)` marker — `item_name` = `requires`. The driver reads it as a
/// precondition over the fully-typed body. No-op at runtime.
#[inline]
pub fn requires(_b: bool) {}

/// `ensures!(b)` marker — `item_name` = `ensures`. The driver reads it as a
/// postcondition over the fully-typed body. No-op at runtime.
#[inline]
pub fn ensures(_b: bool) {}

/// `forall!(|x| p)` marker — `item_name` = `forall`. The driver reads the
/// CLOSURE argument and lowers a real universal quantifier; this `true` body is
/// never its verification meaning. Generic over the closure type only (no bound
/// on its call signature) so any well-formed binder shape type-checks; the
/// driver enforces the typed-scalar-binder whitelist on the THIR side.
#[inline]
pub fn forall<F>(_f: F) -> bool {
    true
}

/// `exists!(|x| p)` marker — `item_name` = `exists`. The driver reads the
/// CLOSURE argument and lowers a real existential quantifier; this `true` body
/// is never its verification meaning.
#[inline]
pub fn exists<F>(_f: F) -> bool {
    true
}
