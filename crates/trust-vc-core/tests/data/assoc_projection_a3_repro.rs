// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the Phase A3 (associated-type projection) adversarial soundness
// suite. A parameter typed by a fully-qualified projection
// `<Concrete as Trait>::Assoc` resolves to the concrete type the impl binds
// (`type Assoc = T;`) at target lifting, landing in the parameter's OWN sort.
//
// The cardinal invariant (the sort-divergence trap): the resolved sort must be
// the sort the impl ACTUALLY binds — never silently coerced to the declared
// abstract slot's sort, nor to an unbounded `int`. So the SAME `<= 255` fact
// that holds for a `u8`-bound projection MUST fail for a `u16`-bound one, and a
// projection resolved to `u16` must range the FULL u16 (bound 65535), not u8.
//
// Every TRUE post-resolution fact must VERIFY; every FALSE fact must
// Counterexample (a false Verified is a cardinal false-verify, and a
// fail-closed Error/Unknown would mean the projection was recognized-but-not-
// resolved — inert recognition, equally a failure of this suite). Verified via
// `verify_function_from_file` in `assoc_projection_a3_soundness.rs`.

#![allow(dead_code, unused_variables)]

#[trust_vc::trait_spec]
trait ProjU8Trait {
    type X;
}

struct ProjU8Struct;

#[trust_vc::trait_impl]
impl ProjU8Trait for ProjU8Struct {
    type X = u8;
}

#[trust_vc::trait_spec]
trait ProjU16Trait {
    type X;
}

struct ProjU16Struct;

#[trust_vc::trait_impl]
impl ProjU16Trait for ProjU16Struct {
    type X = u16;
}

// TARGET analog: the u8-bound projection param upper-bound `<= 255` is a
// tautology for u8 -> Verified. Also proves the resolved type is a BOUNDED
// bitvector, not an unbounded `int` (for which `x <= 255` would Counterexample).
fn param_projection_u8_upper_bound_verified(x: <ProjU8Struct as ProjU8Trait>::X) {
    trust_vc::assert!(x <= 255u8);
}

// The u8 upper value 255 is REACHABLE: `x < 255` must Counterexample. Proves the
// param genuinely ranges the full u8 [0, 255] — the u8 sort is load-bearing, not
// a vacuous/narrowed slot.
fn param_projection_u8_strict_bound_counterexample(x: <ProjU8Struct as ProjU8Trait>::X) {
    trust_vc::assert!(x < 255u8);
}

// FALSE-VERIFY TRAP: the SAME `<= 255` fact that holds for the u8 projection MUST
// FAIL for a projection resolved to u16 (which ranges to 65535). A Verified here
// would mean the u16 projection was given u8 (or unbounded-int) semantics — the
// sort-divergence unsoundness. MUST be Counterexample.
fn param_projection_u16_overstrong_counterexample(x: <ProjU16Struct as ProjU16Trait>::X) {
    trust_vc::assert!(x <= 255u16);
}

// The u16 projection resolves to the FULL u16 range: `x <= 65535` is a tautology
// -> Verified. Together with the CX above this proves the projection resolves to
// a genuine, correctly-sized u16 (not u8, not int) — resolution is per-impl
// exact and load-bearing (ProjU16Struct -> u16, distinct from ProjU8Struct -> u8).
fn param_projection_u16_full_bound_verified(x: <ProjU16Struct as ProjU16Trait>::X) {
    trust_vc::assert!(x <= 65535u16);
}
