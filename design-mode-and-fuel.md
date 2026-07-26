# Design: mode system (#3) + reveal/fuel/by(compute) (#4)

Phased, **MBQI-free** plans from a pure-read design swarm (2026-06-02), keeping
the design pipeline ahead of the build pipeline. Both keep `trust-vc-core`'s
quiescent lib-test baseline (~15807/0/1) green. See
the internal feature backlog, items #3 and #4.

**Cross-cutting dependency:** promotion off `unsupported-gap` for these clusters
is gated on **exact Verus diagnostic-string parity** (`assert_vir_error_msg`
needs verbatim text) — i.e. the backlog **#1 diagnostic-parity layer** is a
prerequisite multiplier for both. Build it alongside.

---

## Backlog #3 — Tracked/Ghost proof/spec/exec mode system (MBQI-free)

Grow from the existing **function-level** mode model (`mode.rs` `FunctionMode` +
`can_call` matrix + `mode_scan` exec-caller audit — the one substantially-built
piece, R8) to a **per-body / per-binding / per-expression** `VarMode` lattice
mirroring Verus. Keystone: a new `crates/trust-vc-core/src/mode_body.rs` pass
computing `Γ: binding → VarMode{Exec,Proof,Ghost,Tracked}` and an
expression-mode inference visitor, invoked from `proof_expand.rs`/`spec_expand.rs`
and exec-fn expansion.

| Ph | Work |
|----|------|
| 0 | Diagnostic-string parity scaffold + `VarMode` lattice (no behavior change; `mode.rs` is `#[non_exhaustive]`). |
| 1 | **Variable-mode tracking** — `let ghost`/`let tracked`, assign/declare-in-exec rules (R3); emit verbatim "exec code cannot mutate non-exec variable", "cannot assign to exec variable from proof mode". **First increment** (smallest sound slice; flips several `modes.rs` cases; no ay change). |
| 2 | Wrapper-expression modes (`Ghost<T>`/`Tracked<T>` `@`/`.view()` spec; `.get()`/`.borrow()` need proof + tracked) + struct/tuple field modes (R1,R2,R4). |
| 3 | Pattern-binding modes (`let tracked X{y,z}`, numeric/out-of-order, or-pattern agreement) + unwrap-parameter desugar (`Ghost(g)`/`Tracked(t)` params) (R5,R6). |
| 4 | `&mut`-argument place modes ("expected mode M, &mut argument has mode N"), never-type-in-spec coercion ban, pure-context purity (R7 partial, R9, R8 purity). |
| 5 | Deferred standalone subfeatures: proof closures (R10, ~70 cases), proof-in-spec (R11), exec_spec codegen (R12). |

- **MBQI-free:** yes. **Unblocks:** modes.rs, never_type.rs, mut_refs_modes.rs, lifetime.rs (move/borrow core).
- **Risks:** diagnostic-string parity is load-bearing; method calls resolved by name only (`validate_function_calls_for_mode` returns None on unknown) — wrapper methods need resolution; exec fns aren't internally mode-checked today; unwrap-parameter desugar must produce the exact header shape.

---

## Backlog #4 — reveal/hide/opaque + fuel + by(compute) (MBQI-free core)

Splits along an MBQI-free / E-matching-bounded line. The **`by(compute)`
interpreter** (`encoder/verification/compute.rs` `ComputeEvaluator`) is a
deterministic recursive partial evaluator that runs **outside the solver** —
extending it needs **no quantifier instantiation at all** (strongest standalone
item). opaque/reveal already works end-to-end via `spec_expand.rs` definitional
axioms; hide()/fuel/modules are the gaps.

| Ph | Work |
|----|------|
| 1 | **`by(compute)` value-domain extension** (MBQI-free, biggest leverage): extend `ComputeEvaluator` beyond Bool/Int/Unit to tuples/structs/field-projection/datatype `Match`/Seq/Set/Map/bitwise/applied closures. **First increment:** add `ComputeValue` variants + `eval_expr` arms for tuples/structs/field-projection and datatype `Match` (catch-all currently returns None on `TrustVcExpr::Match`). |
| 2 | Exact compute recursion-depth diagnostic + `compute_only` failure strings (re-tune `COMPUTE_UNFOLD_LIMIT`=32 so `count_down(50)` succeeds but infinite recursion hits the limit). |
| 3 | `hide()` (dual of reveal, absent today) + reveal-target resolution & legality diagnostics — add a `hide!` macro. |
| 4 | **Per-function fuel + `reveal_with_fuel(f,N)` + default-fuel=1** (E-matching-bounded, NOT MBQI): the uniform implicit fuel-8 over-unfolds; lower to true per-function fuel so insufficient-fuel cases fail as upstream expects. *(Highest baseline-regression risk — gate carefully.)* |
| 5 | Module/visibility model: closed/open/`opaque_outside_module` + privacy diagnostics (largest greenfield; only a bare `is_opaque` bool exists today). |
| 6 | `compute` vs `compute_only` SMT-fallback split (currently conflated on `SolverMode::Compute`) + broadcast-reveal context + cycle diagnostics. |

- **MBQI-free:** core yes (Phase 4 is E-matching/fuel-bounded, not MBQI). **Unblocks:** assert_by_compute.rs, opaque_reveal.rs, inline.rs, modules.rs, broadcast_forall.rs (reveal part), recursion.rs (fuel subset).
- **Risks:** Phase 4 fuel is the central parity+regression risk; promotion needs exact diagnostic strings; Phase 6 SMT-fallback split must not let `compute` accept what `compute_only` rejects (unsoundness).

---

## Recommended interleave

The autonomous loop has, ready to build (all MBQI-free, sound, high-leverage):
1. **#1 diagnostic-parity layer** — prerequisite multiplier (in progress via the #2778 increment).
2. **#2 new-mut-ref Phase 0** — `final()` capture (see [design-new-mut-ref.md](design-new-mut-ref.md)).
3. **#4 `by(compute)` Phase 1** — value-domain extension (standalone, no deps).
4. **#3 mode system Phase 1** — variable-mode tracking.

Research-track (MBQI / NIA / Gröbner) runs in parallel and gates the rest.
