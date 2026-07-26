# Design: new-mut-ref / prophecy core (backlog #2)

Phased, **MBQI-free** implementation plan for the prophecy/new-mut-ref semantic
core — the highest-leverage *sound* engine feature (~17 files, hundreds of
cases). From a read-only design swarm (2026-06-02). Drives the autonomous loop's
next several increments; see the internal feature backlog, item #2.

> Baseline caveat: one design agent reported "63 failing lib tests" — that run
> overlapped a concurrent editing increment mutating `trust-vc-core`, so it is
> contaminated. The authoritative quiescent baseline is **`targo test -p
> trust-vc-core --lib` = 15807 passed / 0 failed / 1 ignored**. Each phase must
> keep that green. (Lesson: design swarms must be pure-read — no `targo test` —
> when an editing workflow is live on the same tree.)

## Core encoding (reuse, don't reinvent)

Each `&mut` place `P` of type `T` gets **two ground terms** of `sort_for_type(T)`
(no quantifiers):
- `cur_P` — the current value (`*P`), SSA-versioned through the body.
- `fin_P` — a **fresh prophecy constant** = the prophesied final value (`*final(P)`).

Reuse the already-wired substrates: the prophecy primitive (`ir_expr.rs`
`ProphecyNew`→`solver.fresh_var`, `ProphecyResolve`→ground `try_eq`;
`encoder/ir_encoder/prophecy.rs`) and the place algebra (`ir_place.rs`
`TrustVcPlace` + `place_disjoint`, which emits only `BoolLit`/`Compare(Ne)` — no
quantifiers). **Retire** the `ErasedMutRefTarget` string-substitution path in
`vc_extraction/body_extract.rs` (don't extend it).

Spec ops map to: `mut_ref_current`/`*P`/`old(*P)`→`cur_P` (entry snapshot / SSA);
the bare binding `P` in a postcondition and `final(*P)`→`fin_P`; `has_resolved(P)`
→ `cur_P == fin_P`. At **every** function exit emit `ProphecyResolve(fin_P ==
current_SSA_value)`.

## Phases (each a sound, independently-testable increment)

| Ph | Work | Key files | Unblocks |
|----|------|-----------|----------|
| **0** | Record the exact quiescent failing-test baseline; add `final(...)` source/macro capture as the symmetric twin of `old(...)` (`OldCaptureKind::{Value,Deref}`). No verification change. | `trust-vc/src/postcondition_lowering.rs`, `ir_expr.rs` | scaffolding |
| **1** | Scalar `&mut` param: `(cur,fin)` prophecy pair, `old()`/`final()`, exit resolution. **FIRST SOUND SLICE.** | `vc_extraction/param_extract.rs`, `body_extract.rs`, `encoder/ir_encoder/prophecy.rs` | mut_refs.rs scalar params, mut_refs_old.rs |
| **2** | Struct/tuple/box field `&mut` places via `TrustVcPlace` + datatype selectors (each field an independent SSA-keyed current + per-field fin). | `body_extract.rs`, `ir_place.rs`, `place_encoding.rs` | test_field_update, mut_refs_patterns.rs |
| **3** | Reborrow chains: child shares parent's current sub-place, fresh `fin_Y`, freeze parent while live; compose via one ground equality. | `body_extract.rs`, `ir_place.rs`, `prophecy.rs` | test_reborrow, temporaries |
| **4** | Control-flow join points: phi the current-SSA coordinate at branch joins (lift the proof-only `MutRefRewriter` depth restriction into the VC layer). | `body_extract.rs`, `mut_ref_proof_rewriter.rs` | control_flow_* |
| **5** | Compositional callee `f(&mut Q)`: bind callee `old`, check `requires`, fresh `fin_call`, assume `ensures`, write back. | `body_extract.rs`, `verification/body_support.rs`, `contract_registry.rs` | mut_refs_libs.rs calls |
| **6** | Array/slice/Vec index `&mut` via ay `try_store`/`try_select` (read-over-write). | `body_extract.rs`, `place_encoding.rs`, `ir_place.rs` | **#2779** mut_refs_slices_arrays.rs, mut_refs_libs.rs |
| **7** | Two-phase borrow resolve-point modeling (resolve after all args evaluated). | `body_extract.rs`, `mut_ref_proof_rewriter.rs` | two_phase_* |
| **8** | Prophetic-context discipline + ghost/tracked modes + backward-compat bridge (mostly exact-error-message parity); keep legacy `arrays.rs`/`slices.rs` `old()`-only semantics passing. | `body_extract.rs`, `proof_stmt_bridge/prophecy.rs`, `postcondition_lowering.rs` | prophecy.rs, modes, unions |

## Soundness tripwires (must hold)

- **fin_P stays unconstrained until the single exit resolution** — never constrain it elsewhere, or proofs become unsound (time-travel).
- **No extensional `==` for `&mut`** — deriving `==` from current+future makes `==` prophetic (mut_ref_not_extensional asserts this is rejected).
- **Exit-resolution completeness** — `ProphecyResolve` must fire on *every* exit path (return, fallthrough, early-return, `?`).
- **Dual-path migration** — Phases 1-6 run the new `(cur,fin)` path beside the surviving `ErasedMutRefTarget` path; the routing predicate must be exact to avoid divergence.
- **Field-as-independent-SSA must still answer whole-struct reads.**
- **`place_disjoint` is static-only** — index places with unknown `i,j` rely on array read-over-write, not disjointness.
- **MBQI-free only while specs are ground** — a ported case whose `ensures` quantifies over a collection escapes to the (MBQI-blocked) quantifier path; keep those out of the core's promotion set.

## Smallest first increment (next editing build)

**Phase 0 only**: (1) record the exact quiescent failing-test baseline so "green"
= "no new failures vs the recorded set"; (2) add `final(...)` capture in
`postcondition_lowering.rs` as the exact symmetric twin of the existing
`old(...)` machinery (`parse_old_capture_group` → `parse_final_capture_group`;
`final(x)`→`Value`, `*final(x_ref)`→`Deref`), with unit tests mirroring the
old-capture tests. Pure plumbing, introduces no verification behavior (the
new-mut-ref flag enables nothing yet), cannot regress.
