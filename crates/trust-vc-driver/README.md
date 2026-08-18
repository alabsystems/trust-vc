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
gate); and (3) the **ay-certificate** capability — independently re-checkable
UNSAT proofs that are trust-vc's soundness edge over Verus's black-box Z3. The
north star is `design-trust-proof-backend.md` at the repo root.

See `design-rustc-driver-frontend.md` (repo root) for the full rationale, ROI bounds,
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
| `lower` | **stable** (root `rust-toolchain.toml`, 1.95.0) | ✅ yes | Driver-independent IR bridge: a fully-typed `DriverFn` → `VerificationContext` → real encoder + ay. The load-bearing, tested seam. |
| `driver` | **Trust toolchain** (`trust`; the fork's stage2 + its `rustc_private` libs) | ❌ no (`feature = "rustc-driver"`) | The real `rustc_driver::Callbacks`: obtains `TyCtxt`, finds verification targets, maps type-checked signatures, walks THIR, feeds `lower`. |

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
libraries — trust-vc is a submodule of the Trust rustc fork, and the driver's
`extern crate rustc_{driver,hir,interface,middle}` resolve from the fork's
`build/` tree. `rustc-dev` is **not** a rustup component on the linked `trust`
toolchain, so a bare `cargo build --features rustc-driver` fails with E0463
("can't find crate for `rustc_*`"). The wrapper script discovers the fork's
rustc_private rlibs + the matching host proc-macro dylibs (the same artifacts
bootstrap collects for clippy/miri-style `rustc_private` tools) and puts them on
rustc's `-L` search path:

```bash
scripts/build-trust-vc-driver.sh          # compile the driver lib (rlib; no link)
scripts/build-trust-vc-driver.sh check    # type-check only
scripts/build-trust-vc-driver.sh test     # build + run the feature tests
```

What the script wires up (all paths are auto-discovered from
`rustc +trust --print sysroot`), with `RUSTC_BOOTSTRAP=1` to permit
`#![feature(rustc_private)]` on the fork rustc:

* `-L <build>/<host>/stage2-rustc/<host>/release/deps` — `librustc_*.{rlib,rmeta}`
  and `librustc_driver.dylib`;
* `-L <build>/<host>/rustc-private-sysroots/<tool-sysroot>/host` — the host
  proc-macro dylibs (`rustc_macros`, `derive_where`, `tracing_attributes`),
  selected by matching the `librustc_middle` build hash to the deps dir;
* `-L native=$(llvm-config --libdir)` and `-L native=$(brew --prefix zstd)/lib`
  — `Polly`/`zstd`/… that linking `rustc_driver` into a binary pulls in.

`build`/`check` scope the `-L` flags to the driver crate (`cargo rustc -- …`) so
the dependency graph stays cached; `test` must put them on global `RUSTFLAGS`
(they have to reach every test binary that links the feature-on lib).

> Toolchain note: `src/driver.rs` targets the **Trust toolchain rustc API**
> (`rustc 1.96.0-dev`): `rustc_driver::run_compiler`, `tcx.hir_free_items()` /
> `hir_item` / `hir_attrs`, and `Attribute::name()`. These are the accessors the
> module's own API-stability caveat anticipated would move when the pin bumped
> off the original stock nightly; stock nightlies are the wrong toolchain here
> (their rustc internals differ from the fork's — see the root
> `rust-toolchain.toml`).

> Status: the driver layer's **signature lowering is wired** (parameter/return
> types come from `tcx.fn_sig`); THIR **body and `requires`/`ensures` lowering**
> is the next increment. Until it lands, the driver is *fail-closed*: it refuses
> a function it cannot fully encode rather than emit a vacuous proof.

## Why this is additive and safe

`trust-vc-driver` is a workspace member, but the `rustc-driver` feature is **off
by default**, so a root `targo --unverified build`/`targo --unverified test` compiles only the stable
`lower` layer and the evidence gate is undisturbed. The nightly pin lives in this
crate's own `rust-toolchain.toml`, which only applies when targo is invoked from
inside this directory.
