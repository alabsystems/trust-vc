# trust-vc-driver

The **typed (rustc-driver) front end** for trust-vc. It lowers Rust into
trust-vc's existing typed IR using the *fully type-checked* program rustc
produces (THIR + `TyCtxt`), instead of reconstructing types from `syn` syntax.

trust-vc is a **submodule of Trust** (the rustc fork); its ultimate role is
Trust's proof-calculus + SMT backend on the pure-Rust **ay** solver. This crate
carries three capabilities toward that role: (1) the shared **`lower` seam** —
the toolchain-independent typed-IR bridge every front end reuses; (2) the
**Verus-compat standalone driver** — a `rustc_driver::Callbacks` front end that
keeps trust-vc a drop-in Verus replacement (the parity benchmark / evidence
gate); and (3) the **ay-certificate** capability — re-checkable UNSAT proofs that
are trust-vc's soundness edge over Verus's black-box Z3. Scope that edge
honestly: `trust-vc-kernel` checks propositional resolution plus structural EUF
(transitivity/congruence) and LRA (Farkas) lemmas, and accepts **NIA, BV, Array
and Seq on trust** (`crates/trust-vc-kernel/src/lib.rs:17`); Alethe is one of its
export formats, not an input it re-checks. The north star is
`design-trust-proof-backend.md` at the repo root.

See `docs/archive/design-rustc-driver-frontend.md` for the full rationale, ROI bounds,
and migration plan. The short version: the dominant reason 100% Verus parity is
hard is an **information ceiling** — the `syn` front end never sees rustc's
types, trait resolution, borrow info, or const-eval, yet most unsupported Verus
features depend on exactly that. Verus solves this by being a rustc driver; this
crate adopts the same architecture **without** adopting Verus's VIR/AIR or Z3:
rustc's THIR is lowered into trust-vc's *own* `TrustVcExpr` IR and verified by
trust-vc's *own* encoder + ay backend + evidence gate. Independence **from
Verus** and the UNSAT-certificate edge are preserved; only the syntax→IR front
half changes.

## Two layers, split by buildability

| Layer | Toolchain | Built by default | Role |
|-------|-----------|------------------|------|
| `lower` | **Trust toolchain** (`channel = "trust"`, the root `rust-toolchain.toml`) — but no `rustc_private` | ✅ yes | Driver-independent IR bridge: a fully-typed `DriverFn` → `VerificationContext` → real encoder + ay. The load-bearing, tested seam. |
| `driver` | **Trust toolchain plus its `rustc_private` half** | ❌ no (`feature = "rustc-driver"`) | The real `rustc_driver::Callbacks`: obtains `TyCtxt`, finds verification targets, maps type-checked signatures, walks THIR, feeds `lower`. |

> Corrected 2026-08-30: this table used to call the `lower` row **stable
> (1.95.0)**, and the closing section used to speak of a "nightly pin" in this
> crate. Neither is true — the workspace pins `channel = "trust"`. What actually
> separates the two rows is `rustc_private`, not the channel. (This crate's own
> duplicate `rust-toolchain.toml` was removed on 2026-09-28; the root pin covers
> it.)

The two layers meet at exactly one type — `lower::DriverFn` — so the
toolchain-pinned rustc glue is thin and replaceable while the reusable lowering
logic is portable and unit-tested.

## Build & test

Default (stable) — compiles and tests the `lower` seam end to end through ay:

```bash
targo --unverified test -p trust-vc-driver
```

The `tests/lower_end_to_end.rs` suite proves the seam is **sound**: valid
postconditions verify, and false ones are refuted with a counterexample (not
rubber-stamped).

The real driver builds against the **Trust toolchain's** `rustc_private`
libraries, which the Trust sysroot serves directly — no `-L` overlay, no
`RUSTC_BOOTSTRAP`, no wrapper script (the `scripts/build-trust-vc-driver.sh`
recipe that assembled them from a Trust `build/` tree was removed on
2026-09-28):

```bash
targo --unverified check -p trust-vc-driver --features rustc-driver   # type-check only
targo --unverified test  -p trust-vc-driver --features rustc-driver   # build + run the feature tests
targo --unverified build -p trust-vc-driver --features rustc-driver --bin trust-vc-driver
```

The bin and every test binary link `librustc_driver-<hash>` from the
compiler's `<sysroot>/lib`; `build.rs` bakes an rpath to that directory into
them (so no `DYLD_LIBRARY_PATH`) and exports the sysroot as
`VC_DRIVER_COMPILER_SYSROOT`, which the driver tests pass as `--sysroot`.

> Toolchain note: `src/driver.rs` targets the **Trust toolchain rustc API**:
> `rustc_driver::run_compiler`, `tcx.hir_free_items()` / `hir_item` /
> `hir_attrs`, and `Attribute::name()`. These are the accessors the module's own
> API-stability caveat anticipated would move when the pin bumped off the
> original stock nightly; stock nightlies are the wrong toolchain here (their
> rustc internals differ from the fork's). The accessor set was re-built against
> the installed Trust toolchain (`1.99.0-dev`, 321aaeda7) on 2026-09-28, after
> last being built against `1.96.0-dev`. Print the live one with
> `trustc --version` rather than reading a number out of this note.

> Status: the driver layer's **signature lowering is wired** (parameter/return
> types come from `tcx.fn_sig`); THIR **body and `requires`/`ensures` lowering**
> is the next increment. Until it lands, the driver is *fail-closed*: it refuses
> a function it cannot fully encode rather than emit a vacuous proof.

## Why this is additive and safe

`trust-vc-driver` is a workspace member, but the `rustc-driver` feature is **off
by default**, so a root `targo --unverified build`/`targo --unverified test`
compiles only the `lower` layer and the evidence gate is undisturbed.
