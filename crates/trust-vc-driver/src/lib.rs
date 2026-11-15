//! trust-vc-driver — the typed front-end seam + Verus-compat rustc driver.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # Context: trust-vc is Trust's proof backend
//!
//! trust-vc is a submodule of **Trust** (`first-party/trust-vc`) and its ultimate
//! role is Trust's proof-calculus + SMT backend on the pure-Rust **ay** solver.
//! Inside Trust, the *primary* front end is **`trust-vc-trust-engine`**, which
//! consumes Trust's compiler IR — **`trust-ir`** — carrying resolved compiler
//! facts (`NativeCompilerFactRef`: types/borrows) and a `ProofCertificate`
//! lineage. See `design-trust-proof-backend.md` (the north star) and
//! `docs/archive/design-rustc-driver-frontend.md` (this crate's front end).
//!
//! This crate hosts two things:
//!
//! 1. **The shared lowering seam** ([`lower::DriverFn`]) — a fully-typed function
//!    model → `VerificationContext` → the existing encoder/ay backend. Both the
//!    in-Trust path and the standalone driver target this one type, so the
//!    information that the legacy `syn` reader had to reconstruct by hand
//!    (types/traits/borrows/const) arrives already resolved.
//! 2. **The Verus-compatibility front end** — a standalone `rustc_driver` for
//!    verifying vanilla-rustc / the Verus corpus *outside* Trust (the parity
//!    benchmark). Inside Trust, the compiler facts come over `trust-ir` instead,
//!    so this driver's nightly/`rustc_private` cost does not apply to the product.
//!
//! ## The soundness edge over Verus (built here)
//!
//! With `feature = "certificates"`, [`lower::DriverFn::verify_certified`] returns
//! an **ay UNSAT proof re-checked by `trust-vc-kernel`** ([`lower::Certificate`],
//! `kernel_verified`). Verus trusts Z3's answer with no checkable artifact; every
//! trust-vc "Verified" can carry a certificate that flows into Trust's
//! `trust_ir::ProofCertificate` lineage. This is capability #1 of the superiority
//! roadmap in the north-star design.
//!
//! # Layering (by buildability)
//!
//! * [`lower`] — the **driver-independent** IR bridge. Given a [`lower::DriverFn`]
//!   that already carries resolved [`trust_vc_core::ir::TrustVcType`]s, it builds
//!   a [`trust_vc_core::vc::VerificationContext`] and runs the real backend. This
//!   compiles and is tested on the pinned **stable** toolchain — it is the
//!   load-bearing proof that "typed front-end input → existing backend → sound
//!   verdict" works end to end.
//! * `driver` — the real `rustc_driver::Callbacks` that obtains `TyCtxt`, finds
//!   verification targets, walks THIR, and produces [`lower::DriverFn`]s. It is
//!   gated behind `feature = "rustc-driver"` and the Trust toolchain's
//!   `rustc_private` crates (which its sysroot serves), so the default build
//!   stays dependency-light.
//!
//! The two layers meet at exactly one type — [`lower::DriverFn`] — so the hard,
//! toolchain-pinned rustc glue is thin and replaceable while the reusable
//! lowering logic is portable and unit-tested.

// The `rustc_private` feature is only valid on nightly, so it must not appear in
// the default (stable) build. It is enabled only when the `rustc-driver` feature
// compiles `driver.rs`.
#![cfg_attr(feature = "rustc-driver", feature(rustc_private))]

pub mod lower;

#[cfg(feature = "rustc-driver")]
pub mod driver;

// --- Superiority capabilities (design-trust-proof-backend.md §5a) ---
// Each is feature-gated and additive; the default build compiles only `lower`.

/// #3 Certified cross-crate proof cache (kernel-checked certificates, content-keyed).
#[cfg(feature = "cache")]
pub mod cache;

/// #4 Native collection decision procedures (Seq/Set/Map/Multiset via ay theories).
#[cfg(feature = "collections")]
pub mod collections;

/// #5 Exact string/byte proofs (String/str + Seq + BV).
#[cfg(feature = "strings")]
pub mod strings;

/// #6 Bit-precise unsafe/layout contracts (size/align/niche + BV facts).
#[cfg(feature = "layout")]
pub mod layout;

/// #7 Solver-specialization hook (VC-shape → strategy; ay-JIT counterpart).
#[cfg(feature = "tactics")]
pub mod tactics;

/// #2 Compiler-fact frame/alias VCs from Trust's compiler IR (`trust-ir`).
#[cfg(feature = "trust-integration")]
pub mod compiler_facts;
