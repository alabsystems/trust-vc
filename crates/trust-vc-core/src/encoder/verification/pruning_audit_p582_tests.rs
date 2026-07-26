//! Strategic audit report — P1-582 (continuation of P1-581).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Prover audit of 6 production modules totaling ~3,539 lines.
//! All modules found SOUND. No soundness bugs discovered.
//!
//! ## Modules Audited
//!
//! 1. **obligation_collection.rs** (598 lines) — Thread-local obligation
//!    collection with borrow-conflict graceful skip. SOUND: fail-closed
//!    guard in `finalize_verify_result()` (verification_bridge.rs:128-134)
//!    forces `VerifyResult::Unknown` when any obligations are dropped,
//!    preventing silently skipped assertions. #2360 counter tracks drops.
//!
//! 2. **ground_pool.rs** (529 lines) — Eager ground-term instantiation
//!    of broadcast axioms. SOUND: deduplication via `seen_entries` HashSet,
//!    arity matching prevents binding mismatches, `reset_flush_state()`
//!    correctly handles push/pop solver reuse. 10 tests with good coverage.
//!
//! 3. **ground_seeding.rs** (188 lines, 98 production) — Collection ground
//!    select seeding. SOUND: seeds `select(array, 0)` via fresh unconstrained
//!    constant. Always satisfiable. 2 tests.
//!
//! 4. **verification_bridge.rs** (523 lines) — Proc-macro to VC pipeline
//!    bridge. SOUND: all `verify()` exit paths wrapped by
//!    `finalize_verify_result()`. Collection errors return `Error` (not
//!    `Verified`). Context snapshot via clone provides isolation.
//!
//! 5. **recursion_graph.rs** (698 lines) — Tarjan SCC for mutual recursion
//!    detection. SOUND: standard textbook Tarjan implementation. Self-loops
//!    handled correctly (1-element SCC with self-edge check). Conservative
//!    under-approximation: unresolved calls are skipped, so some recursion
//!    may not be detected (completeness issue, not soundness). 9 tests.
//!
//! 6. **mut_ref_proof.rs** (1003 lines) — SSA-style shadow variable
//!    rewriting for `&mut` parameters in proof bodies. SOUND: stores
//!    restricted to top-level only (nested_block_depth==0 &&
//!    control_flow_depth==0); unsupported patterns rejected with compile
//!    errors. RHS of stores fold through current version before bump.
//!    `old!()` resolves to entry shadow (version 0). Field-place granularity
//!    tracks independent versions per field. 12+ tests.
//!
//! ## Observations (not bugs)
//!
//! - `register_proof` in verification_bridge.rs uses `borrow_mut()` (panics
//!   on conflict) while `register_collection_error` uses `try_borrow_mut()`
//!   (graceful skip). Inconsistency but not a bug — registration functions
//!   are called at a higher level where borrow conflicts don't occur.
//!
//! - `parse_solver_mode` in obligation_collection.rs:596 maps unknown mode
//!   strings to `SolverMode::Default` silently. Not a soundness issue
//!   (Default is the most conservative mode) but could confuse users who
//!   typo a mode name.
//!
//! - `collect_let_binding_runtime_value_from_ref` silently skips unsupported
//!   types (neither bool nor integer). The let binding value is unconstrained
//!   from the solver's perspective. Completeness issue only — solver considers
//!   more values than possible, making proofs harder, not unsound.
//!
//! ## Filed Issues
//!
//! - **#2524** (P3 bug): pruning_audit_tests.rs module registration +
//!   triggerless broadcasts test fix. Two Worker items from P1-581 audit.

#[cfg(test)]
mod report_anchor {
    #[test]
    fn audit_report_p582_compiled() {
        // This test exists to prove the audit report compiles.
        // Audit findings documented in module-level doc comments above.
    }
}
