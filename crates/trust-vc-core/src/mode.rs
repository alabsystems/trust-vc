//! Function mode system — exec/proof/spec mode classification and enforcement.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Implements Verus-style function mode classification. Every function in a
//! trust-vc-annotated crate is one of:
//!
//! - **Exec**: normal runtime code (default, no annotation)
//! - **Proof**: ghost proof code (`#[trust_vc::proof]`), erased at runtime
//! - **Spec**: pure specification code (`#[trust_vc::spec]`), erased at runtime
//!
//! The mode matrix governs which cross-mode calls are legal:
//!
//! | Caller | Can call Exec | Can call Proof | Can call Spec |
//! |--------|:---:|:---:|:---:|
//! | Exec   | Yes | No  | No  |
//! | Proof  | No  | Yes | Yes |
//! | Spec   | No  | No  | Yes |
//!
//! Part of #2052, #1573.

#[cfg(test)]
use crate::error::{TrustVcError, TrustVcResult};
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

/// Classification of a function's mode in the Verus mode system.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum FunctionMode {
    /// Normal runtime code. Default for unannotated functions.
    Exec,
    /// Proof function (`#[trust_vc::proof]`). Can call proof and spec functions.
    /// Erased at runtime.
    Proof,
    /// Specification function (`#[trust_vc::spec]`). Can only call other spec
    /// functions. Erased at runtime.
    Spec,
}

impl FunctionMode {
    /// Returns whether `self` (the caller) may call a function with mode `callee`.
    #[must_use]
    pub fn can_call(self, callee: FunctionMode) -> bool {
        match (self, callee) {
            // Exec can only call exec
            (FunctionMode::Exec, FunctionMode::Exec) => true,
            (FunctionMode::Exec, _) => false,
            // Proof can call proof and spec
            (FunctionMode::Proof, FunctionMode::Exec) => false,
            (FunctionMode::Proof, FunctionMode::Proof) => true,
            (FunctionMode::Proof, FunctionMode::Spec) => true,
            // Spec can only call spec
            (FunctionMode::Spec, FunctionMode::Spec) => true,
            (FunctionMode::Spec, _) => false,
        }
    }

    /// Returns a human-readable description of the mode.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            FunctionMode::Exec => "exec",
            FunctionMode::Proof => "proof",
            FunctionMode::Spec => "spec",
        }
    }
}

impl std::fmt::Display for FunctionMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Classification of a **variable / binding / expression** mode in the Verus
/// mode system.
///
/// This is distinct from [`FunctionMode`] (which classifies whole functions).
/// Verus tracks a per-binding mode for every `let` declaration inside a body,
/// and the body-level mode checker ([`crate::mode_body`]) uses this lattice to
/// implement the assign/declare-in-exec rules (backlog #3, R3).
///
/// Verus's underlying `vir::ast::Mode` has only three values — `Spec`,
/// `Proof`, `Exec` — ordered `Exec <= Proof <= Spec`. Surface Verus introduces
/// two binding keywords that project onto that core lattice:
///
/// - `let ghost x`   → a **spec**-mode variable  → [`VarMode::Ghost`]
/// - `let tracked x` → a **proof**-mode variable → [`VarMode::Tracked`]
/// - `let x`         → an **exec**-mode variable → [`VarMode::Exec`]
///
/// [`VarMode::Proof`] is the explicit proof-context mode (e.g. the outer mode
/// of an assignment inside a `proof { ... }` block). For lattice purposes it
/// coincides with [`VarMode::Tracked`] — both project to the core `Proof`
/// mode. Keeping them as separate variants preserves the surface distinction
/// the design calls for (`VarMode{Exec, Proof, Ghost, Tracked}`) while the
/// lattice operations work on the faithful three-valued projection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum VarMode {
    /// Non-ghost, compiled variable. Default for `let x` in exec code.
    Exec,
    /// Proof-context mode (e.g. inside a `proof { ... }` block). Projects to
    /// the core `Proof` mode, the same as [`VarMode::Tracked`].
    Proof,
    /// Spec-mode (`let ghost x`) variable. Erased at runtime. Projects to the
    /// core `Spec` mode.
    Ghost,
    /// Proof-mode (`let tracked x`) variable. Erased at runtime. Projects to
    /// the core `Proof` mode.
    Tracked,
}

/// The faithful three-valued Verus core mode (`Exec <= Proof <= Spec`),
/// onto which [`VarMode`] projects for lattice operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum CoreMode {
    Exec,
    Proof,
    Spec,
}

impl VarMode {
    /// Projects this variable mode onto Verus's three-valued core mode.
    fn core(self) -> CoreMode {
        match self {
            VarMode::Exec => CoreMode::Exec,
            VarMode::Proof | VarMode::Tracked => CoreMode::Proof,
            VarMode::Ghost => CoreMode::Spec,
        }
    }

    /// The lattice order `Exec <= Proof <= Spec` (mirrors Verus `mode_le`).
    ///
    /// Returns whether `self` is *below or equal to* `other`.
    #[must_use]
    pub fn le(self, other: VarMode) -> bool {
        match (self.core(), other.core()) {
            (_, CoreMode::Spec) => true,
            (CoreMode::Exec, _) => true,
            (a, b) => a == b,
        }
    }

    /// The least upper bound of two modes (mirrors Verus `mode_join`).
    #[must_use]
    pub fn join(self, other: VarMode) -> VarMode {
        match (self.core(), other.core()) {
            (_, CoreMode::Spec) | (CoreMode::Spec, _) => VarMode::Ghost,
            (CoreMode::Exec, _) => other,
            (_, CoreMode::Exec) => self,
            (CoreMode::Proof, CoreMode::Proof) => VarMode::Proof,
        }
    }

    /// Whether this mode is the executable (compiled) mode.
    #[must_use]
    pub fn is_exec(self) -> bool {
        matches!(self.core(), CoreMode::Exec)
    }

    /// Human-readable mode name used in diagnostics — matches the spelling
    /// Verus uses in its `cannot assign to {mode} variable from {mode} mode`
    /// diagnostic (`exec` / `proof` / `spec`).
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self.core() {
            CoreMode::Exec => "exec",
            CoreMode::Proof => "proof",
            CoreMode::Spec => "spec",
        }
    }
}

impl std::fmt::Display for VarMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Registry of known function modes, populated during macro expansion.
///
/// The registry uses thread-local storage for the same reason as
/// `VerificationContext`: proc macro expansions happen on the compiler thread,
/// and test-time verification runs on the test thread. Both need access to
/// the registry within a single compilation unit.
///
/// Functions not in the registry are assumed to be `Exec`.
///
/// **Compile-time vs runtime (#2300):** For compile-time legality of
/// same-module functions, `mode_scan` scans the source file to build an
/// order-independent mode table. The compile-time registry
/// (`COMPILE_TIME_MODE_REGISTRY`) is consulted only for non-local items.
/// The runtime/test registry (`MODE_REGISTRY`) still defaults unknown
/// names to `Exec` — this is correct for runtime dispatch.
pub(crate) struct ModeRegistry {
    functions: HashMap<String, FunctionMode>,
}

impl ModeRegistry {
    /// Creates an empty registry.
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
        }
    }

    /// Registers a function's mode.
    pub fn register(&mut self, name: impl Into<String>, mode: FunctionMode) {
        self.functions.insert(name.into(), mode);
    }

    /// Returns the mode of a function, defaulting to `Exec` if unknown.
    #[cfg(test)]
    pub fn mode_of(&self, name: &str) -> FunctionMode {
        self.functions
            .get(name)
            .copied()
            .unwrap_or(FunctionMode::Exec)
    }

    /// Returns the mode of a function, or `None` if not registered.
    pub fn get(&self, name: &str) -> Option<FunctionMode> {
        self.functions.get(name).copied()
    }
}

impl Default for ModeRegistry {
    fn default() -> Self {
        Self::new()
    }
}

// ========================================================================
// Thread-local global registry
// ========================================================================

thread_local! {
    static MODE_REGISTRY: RefCell<ModeRegistry> = RefCell::new(ModeRegistry::new());
}

// Compile-time registry used during proc-macro expansion.
//
// Unlike MODE_REGISTRY (thread-local runtime/test state), this registry is
// process-global because macro expansion happens in the compiler host process.
// It tracks mode declarations seen so far in the current compilation unit.
static COMPILE_TIME_MODE_REGISTRY: OnceLock<Mutex<ModeRegistry>> = OnceLock::new();

fn compile_time_registry() -> &'static Mutex<ModeRegistry> {
    COMPILE_TIME_MODE_REGISTRY.get_or_init(|| Mutex::new(ModeRegistry::new()))
}

/// Registers a function's mode in the thread-local registry.
///
/// Called from expanded proc macro code at test time.
#[doc(hidden)]
pub fn register_function_mode(name: &str, mode: FunctionMode) {
    MODE_REGISTRY.with(|reg| reg.borrow_mut().register(name, mode));
}

/// Looks up a function's mode from the thread-local registry.
///
/// Returns `Exec` for unregistered functions.
#[cfg(test)]
#[must_use]
pub(crate) fn lookup_function_mode(name: &str) -> FunctionMode {
    MODE_REGISTRY.with(|reg| reg.borrow().mode_of(name))
}

/// Checks whether calling `callee_name` from `caller_mode` is permitted.
///
/// Returns `Ok(())` if the call is legal, or `Err(TrustVcError::Encoding)`
/// describing the violation if not.
///
/// Part of #1690: returns `TrustVcResult` instead of `Result<(), String>`.
/// Only called from tests currently; production mode checking uses
/// `validate_function_calls_for_mode` in lib.rs which inlines the logic.
#[cfg(test)]
pub(crate) fn check_call(caller_mode: FunctionMode, callee_name: &str) -> TrustVcResult<()> {
    let callee_mode = lookup_function_mode(callee_name);
    if caller_mode.can_call(callee_mode) {
        Ok(())
    } else {
        Err(TrustVcError::Encoding {
            context: "mode check",
            detail: format!(
                "{} function cannot call {} function `{}`",
                caller_mode, callee_mode, callee_name
            ),
        })
    }
}

/// Clears the thread-local mode registry.
///
/// Used between tests to prevent state leakage.
pub(crate) fn clear_mode_registry() {
    MODE_REGISTRY.with(|reg| *reg.borrow_mut() = ModeRegistry::new());
}

/// Registers a function mode in the compile-time macro expansion registry.
pub(crate) fn register_compile_time_function_mode(name: &str, mode: FunctionMode) {
    let mut registry = compile_time_registry()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    registry.register(name, mode);
}

/// Looks up a function mode from the compile-time macro expansion registry.
pub(crate) fn lookup_compile_time_function_mode(name: &str) -> Option<FunctionMode> {
    let registry = compile_time_registry()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    registry.get(name)
}

#[cfg(test)]
pub(crate) fn clear_compile_time_mode_registry() {
    let mut registry = compile_time_registry()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    *registry = ModeRegistry::new();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_exec_can_call_exec() {
        assert!(FunctionMode::Exec.can_call(FunctionMode::Exec));
    }

    #[test]
    fn test_exec_cannot_call_proof() {
        assert!(!FunctionMode::Exec.can_call(FunctionMode::Proof));
    }

    #[test]
    fn test_exec_cannot_call_spec() {
        assert!(!FunctionMode::Exec.can_call(FunctionMode::Spec));
    }

    #[test]
    fn test_proof_cannot_call_exec() {
        assert!(!FunctionMode::Proof.can_call(FunctionMode::Exec));
    }

    #[test]
    fn test_proof_can_call_proof() {
        assert!(FunctionMode::Proof.can_call(FunctionMode::Proof));
    }

    #[test]
    fn test_proof_can_call_spec() {
        assert!(FunctionMode::Proof.can_call(FunctionMode::Spec));
    }

    #[test]
    fn test_spec_cannot_call_exec() {
        assert!(!FunctionMode::Spec.can_call(FunctionMode::Exec));
    }

    #[test]
    fn test_spec_cannot_call_proof() {
        assert!(!FunctionMode::Spec.can_call(FunctionMode::Proof));
    }

    #[test]
    fn test_spec_can_call_spec() {
        assert!(FunctionMode::Spec.can_call(FunctionMode::Spec));
    }

    #[test]
    fn test_registry_default_is_exec() {
        let registry = ModeRegistry::new();
        assert_eq!(registry.mode_of("unknown_fn"), FunctionMode::Exec);
    }

    #[test]
    fn test_registry_register_and_lookup() {
        let mut registry = ModeRegistry::new();
        registry.register("my_proof", FunctionMode::Proof);
        registry.register("my_spec", FunctionMode::Spec);
        assert_eq!(registry.mode_of("my_proof"), FunctionMode::Proof);
        assert_eq!(registry.mode_of("my_spec"), FunctionMode::Spec);
        assert_eq!(registry.mode_of("other"), FunctionMode::Exec);
    }

    #[test]
    fn test_thread_local_registry() {
        clear_mode_registry();
        register_function_mode("helper_spec", FunctionMode::Spec);
        assert_eq!(lookup_function_mode("helper_spec"), FunctionMode::Spec);
        assert_eq!(lookup_function_mode("unknown"), FunctionMode::Exec);
        clear_mode_registry();
    }

    #[test]
    fn test_check_call_legal() {
        clear_mode_registry();
        register_function_mode("spec_fn", FunctionMode::Spec);
        assert!(check_call(FunctionMode::Proof, "spec_fn").is_ok());
        clear_mode_registry();
    }

    #[test]
    fn test_check_call_violation() {
        clear_mode_registry();
        register_function_mode("proof_fn", FunctionMode::Proof);
        let err_msg = check_call(FunctionMode::Exec, "proof_fn")
            .expect_err("exec calling proof should be a mode violation")
            .to_string();
        assert!(
            err_msg.contains("exec function cannot call proof function"),
            "error should describe mode violation: {}",
            err_msg
        );
        clear_mode_registry();
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", FunctionMode::Exec), "exec");
        assert_eq!(format!("{}", FunctionMode::Proof), "proof");
        assert_eq!(format!("{}", FunctionMode::Spec), "spec");
    }

    // --- VarMode lattice (backlog #3, R3) ---

    #[test]
    fn var_mode_le_is_exec_proof_spec_chain() {
        // Exec <= Proof <= Spec (Ghost projects to Spec, Tracked to Proof).
        assert!(VarMode::Exec.le(VarMode::Exec));
        assert!(VarMode::Exec.le(VarMode::Tracked));
        assert!(VarMode::Exec.le(VarMode::Ghost));
        assert!(VarMode::Tracked.le(VarMode::Ghost));
        assert!(VarMode::Tracked.le(VarMode::Tracked));
        assert!(VarMode::Ghost.le(VarMode::Ghost));
    }

    #[test]
    fn var_mode_le_rejects_upward_violations() {
        // proof is NOT <= exec; spec is NOT <= exec or proof.
        assert!(!VarMode::Tracked.le(VarMode::Exec));
        assert!(!VarMode::Proof.le(VarMode::Exec));
        assert!(!VarMode::Ghost.le(VarMode::Exec));
        assert!(!VarMode::Ghost.le(VarMode::Tracked));
        assert!(!VarMode::Ghost.le(VarMode::Proof));
    }

    #[test]
    fn var_mode_proof_and_tracked_share_the_core_proof_mode() {
        // The surface distinction is preserved, but they are lattice-equal.
        assert!(VarMode::Proof.le(VarMode::Tracked));
        assert!(VarMode::Tracked.le(VarMode::Proof));
        assert_eq!(VarMode::Proof.as_str(), "proof");
        assert_eq!(VarMode::Tracked.as_str(), "proof");
    }

    #[test]
    fn var_mode_join_is_least_upper_bound() {
        assert_eq!(VarMode::Exec.join(VarMode::Tracked), VarMode::Tracked);
        assert_eq!(VarMode::Exec.join(VarMode::Ghost), VarMode::Ghost);
        assert_eq!(VarMode::Tracked.join(VarMode::Exec), VarMode::Tracked);
        assert_eq!(VarMode::Tracked.join(VarMode::Ghost), VarMode::Ghost);
        assert_eq!(VarMode::Ghost.join(VarMode::Tracked), VarMode::Ghost);
        assert_eq!(VarMode::Exec.join(VarMode::Exec), VarMode::Exec);
        assert_eq!(VarMode::Tracked.join(VarMode::Tracked), VarMode::Proof);
    }

    #[test]
    fn var_mode_is_exec_only_for_exec() {
        assert!(VarMode::Exec.is_exec());
        assert!(!VarMode::Proof.is_exec());
        assert!(!VarMode::Ghost.is_exec());
        assert!(!VarMode::Tracked.is_exec());
    }

    #[test]
    fn var_mode_display_maps_to_core_mode_names() {
        assert_eq!(format!("{}", VarMode::Exec), "exec");
        assert_eq!(format!("{}", VarMode::Proof), "proof");
        assert_eq!(format!("{}", VarMode::Tracked), "proof");
        assert_eq!(format!("{}", VarMode::Ghost), "spec");
    }
}
