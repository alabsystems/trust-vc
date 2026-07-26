# Design: wiring the mut-ref/mode substrate into the live path

The committed `mut_ref_prophecy.rs` (cur,fin) substrate and `mode_body.rs`
VarMode checker are sound but **unwired** (`#![allow(dead_code)]`, zero
production callers). This is the precise seam map + sound wiring plan (read-only
swarm, 2026-06-02) so the next editing increment turns substrate into promotions.

## Mode wiring — the SMALLEST sound first increment (do first)

**Wire `check_body_var_modes` (mode_body.rs:151) into `mode_scan::validate_mode`
(mode_scan/mod.rs:37-110)** — the single chokepoint shared by all four live
`expand_*` proc-macro sites. After `validate_mode` gathers its existing
call-legality errors, call `check_body_var_modes` on the body's brace-inner token
stream (built from `block.stmts`, NOT `quote!(#block)`); on `Err`, push
`syn::Error::new(input.sig.ident.span(), err.to_string()).to_compile_error()`
into the returned `errors` vec; remove `#![allow(dead_code)]` (mode_body.rs:61) in
the **same** change (so a real caller exists).

- **Mode diagnostics are COMPILE errors** (proc-macro path), NOT
  `VerifyResult::Error` — the premise "surfaces as VerifyResult::Error" is FALSE
  on the live path. Validate with **trybuild compile-fail** fixtures
  (`crates/trust-vc/tests/`, `proof_unsafe_compile_fail.rs` pattern).
- **Monotone-safe:** the checker only ADDS R3 rejections it can prove; unknown
  names (incl. params) default to `VarMode::Exec` (mode_body.rs:135-140,258), so
  inserting it can't reject previously-accepted valid code.
- **Risk — diagnostic-string drop:** preserve the verbatim Verus strings
  (`EXEC_MUTATE_NON_EXEC` mode_body.rs:70; "cannot assign to {x_mode} variable
  from {outer_mode} mode") through the compile-error adapter (`mode_error`
  mode_body.rs:354-360 currently drops the span — wrap to keep the exact text).
- **Defer:** param-mode seeding (signature is body-only today) and the
  `if spec-condition {...}` rule-2 form (mode_body.rs:44-50). Only promote cases
  the checker actually models (proof{...}-block + bare-local assigns).

## Mut-ref wiring — harder (8 steps; after mode-wiring)

Retire the live `ErasedMutRefTarget` string-substitution for SUPPORTED scalar
`&mut` params and route them onto the (cur,fin) substrate. Seams:
- **READ `*P`**: body_extract.rs:1657-1666 (Deref-collapse renders both `*P` and
  bare `P` to `lookup_scoped(P)`). Split: `*P`/`old(*P)`/`mut_ref_current` →
  `current_value_term`; bare `P`/`final(*P)` in postcondition → `final_value_term`.
- **WRITE `*P=rhs`**: visit_expr_assign (3514-3546) → assign_expr (1066-1068) →
  `assign_mut_ref_target` Local arm (1276-1308) — destructive `assign_scoped`
  becomes a re-version of `cur_P` (new SSA term), `fin_P` untouched until exit.
- **PREREQUISITE — exit enumeration:** the live path has NO exit set (`finish()`
  240-245 emits nothing; return wired at vc_extraction.rs:330-360). Must build one
  to emit `exit_resolution_obligation(...)` per exit.
- **ALIAS fabric (highest risk):** `erased_mut_ref_aliases_targeting`
  (1342-1354) + registration (3213-3237) share one mutable string across aliases;
  under (cur,fin) all aliases of P must resolve reads to `cur_P`'s current SSA and
  writes re-version a shared coordinate.
- **old() reject:** lift the hard reject (1723-1725) ONLY for `old(*P)` of a
  migrated param.
- **Namespace:** substrate `__trust_vc_fin_{param}` (mut_ref_prophecy.rs:69) vs
  runtime-path `__trust_vc_final_{var}`/`__trust_vc_old_{var}` (let_bindings.rs) —
  reconcile.
- **Un-gate `#![allow(dead_code)]` only after a real caller exists.**

## Soundness tripwires (both)
- **Dual-path double-constraint:** legacy + (cur,fin) paths must not BOTH
  constrain a migrated param (double-count / divergence). Migrate a param fully or
  not at all.
- **fin_P constrained by EXACTLY ONE equality** (the exit resolution) — the legacy
  implicit "final == current" must be removed for migrated params.
- **Exit-resolution completeness:** every exit path must resolve, or fin_P stays
  free and a postcondition over it is vacuously satisfiable (unsound).
- **Premature un-gating** would let the module compile-decay back to unwired.

## Order
1. Mode-wiring first increment (compile-fail tests; flips modes.rs R3 cases).
2. Mut-ref: exit-enumeration → read/write split for one scalar param (end-to-end
   test: `*P=5; ensures *final(P)==5` verifies; negative twin fails) → alias
   fabric → un-gate.
