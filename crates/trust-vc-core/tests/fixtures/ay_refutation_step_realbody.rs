// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// =====================================================================
// NON-VACUOUS native-deductive proof that the in-production cutting-planes
// REFUTATION SELF-CHECK (`crates/ay-pb/src/proof/refutation_check.rs`)
// ACCEPTS ONLY SOUND STEPS — every derivation step the checker recomputes
// is an entailment-preserving cutting-planes rule, matching the kernel
// arrows in `proofs/clean-pb/PBCertificateAlgebra.lean`
// (`ay_certcut_pb_add_sound` / `_scaling_sound` / `_rounding_sound` /
// `_rhs_weaken_sound` / `_zero_bound_refutation_sound`). Discharged by
// trust-vc on the pure-Rust `ay` SMT solver, kernel-rechecked.
// =====================================================================
//
// WHAT "the checker accepts only sound steps" MEANS HERE
// -----------------------------------------------------
// `refutation_check::replay_derivation` (refutation_check.rs:315-347) recomputes
// each `RefStep` from scratch via the `LinConstraint` rule methods and pushes the
// result; `Refutation::check` (refutation_check.rs:299-306) accepts iff the LAST
// constraint is `0 >= c` with `c >= 1`. So the refutation is sound iff
//   (1) every rule (`add`/`scale`/`divide_ceil`/`saturate`) is ENTAILMENT-
//       PRESERVING: at every 0/1 point that satisfies the operand constraint(s),
//       the recomputed result constraint is also satisfied; and
//   (2) the terminal `0 >= c (c>=1)` is genuinely UNSATISFIABLE.
// This fixture PROVES (1) for add/scale/divide and (2), each at the per-step
// (single-point) level — the soundness CRUX of the kernel arrows. The
// BTreeMap-merge that realizes the per-variable LHS transform inside each rule
// (the n-ary summation) is the whole-loop boundary; the per-step ARITHMETIC
// content of each arrow (the part the kernel theorem proves) is what is verified.
//
// WHY THE LEMMAS ARE OVER `int` (Verus mathematical ℤ), NOT i128
// -------------------------------------------------------------
// The kernel algebra (`PBCertificateAlgebra.lean`) is over ℤ/Prop. The Rust
// checker uses i128 with `checked_add`/`checked_mul`/`checked_div_euclid` and the
// `?` operator: any i128 OVERFLOW makes a rule return `None`, so `replay_derivation`
// REJECTS that step (`RefError::BadStep`). Therefore every step the checker
// ACCEPTS performed exact (non-overflowing) integer arithmetic, which coincides
// with these `int` (ℤ) operations. Stating soundness over `int` is exactly the
// regime the checker operates in (and avoids spurious finite-width wraparound
// "counterexamples" that the checker itself rejects via `checked_*` -> `None`).
//
// MULTIPLICATIVE STEPS AND THE `lemma_*` ARITHMETIC AXIOMS
// -------------------------------------------------------
// `ay` (like every SMT backend) is incomplete on nonlinear integer arithmetic
// (NIA): the products `k * eval` (scale) and `q * d` / `(q+1) * d` (division) are
// not decided automatically. They are supplied as standard, kernel-trivial ring
// facts via `#[trust_vc::external_body]` lemmas (the Verus `vstd::arithmetic`
// pattern): multiplication monotonicity and distributivity. Each lemma's
// `#[requires]` is a CHECKED obligation at the call site (so the axiom cannot be
// misapplied — see the `scale_sound_general` non-vacuity note), and the proof
// then closes by LINEAR reasoning. The `..._no_lemma` control below shows the
// lemma is load-bearing (the same body without it does NOT verify).
//
// HOW THIS IS VERIFIED: `trust_vc_core::verify_function_from_file(<this file>,
// <fn>)`. `Verified` == ay returned UNSAT and the trust-vc-kernel accepted the
// proof; `Counterexample` == ay returned a concrete falsifying model.

// =====================================================================
// VERBATIM real checker source (copied from crates/ay-pb/src/proof/
// refutation_check.rs; a later step diff-checks these blocks against the
// live source). The soundness LEMMAS below mirror these bodies' arithmetic.
// =====================================================================
//
// --- impliedGe_add (refutation_check.rs:126-134) ---
//   /// `impliedGe_add`: pointwise sum of two `>=` facts.
//   fn add(&self, other: &Self) -> Option<Self> {
//       let mut out = self.clone();
//       for (&var, &delta) in &other.coeff {
//           out.add_coeff(var, delta)?;
//       }
//       out.rhs = out.rhs.checked_add(other.rhs)?;
//       Some(out)
//   }
//
// --- impliedGe_scale (refutation_check.rs:136-146) ---
//   /// `impliedGe_scale`: multiply a `>=` fact by a positive scalar `k >= 1`.
//   fn scale(&self, k: i128) -> Option<Self> {
//       if k < 1 {
//           return None;
//       }
//       let mut out = Self::constant(self.rhs.checked_mul(k)?);
//       for (&var, &c) in &self.coeff {
//           out.add_coeff(var, c.checked_mul(k)?)?;
//       }
//       Some(out)
//   }
//
// --- impliedGe_division (refutation_check.rs:148-159) ---
//   /// `impliedGe_division`: divide by `d >= 1`, rounding every coefficient and
//   /// the RHS UP (ceiling). Sound for arbitrary integer coefficients.
//   fn divide_ceil(&self, d: i128) -> Option<Self> {
//       if d < 1 {
//           return None;
//       }
//       let mut out = Self::constant(ceil_div(self.rhs, d)?);
//       for (&var, &c) in &self.coeff {
//           out.add_coeff(var, ceil_div(c, d)?)?;
//       }
//       Some(out)
//   }
//
// --- ceil_div (refutation_check.rs:206-217) ---
//   fn ceil_div(a: i128, d: i128) -> Option<i128> {
//       if d < 1 {
//           return None;
//       }
//       let q = a.checked_div_euclid(d)?;
//       let r = a.checked_rem_euclid(d)?;
//       if r == 0 {
//           Some(q)
//       } else {
//           q.checked_add(1)
//       }
//   }
//
// --- pb_unsat_of_contradictory_bounds (refutation_check.rs:181-185) ---
//   /// `pb_unsat_of_contradictory_bounds`: `true` iff this is `0 >= c` with
//   /// `c >= 1` — an unsatisfiable constraint, hence a refutation.
//   fn is_contradiction(&self) -> bool {
//       self.coeff.is_empty() && self.rhs >= 1
//   }
// =====================================================================

// ---------------------------------------------------------------------------
// Kernel-trivial ring axioms (Verus `vstd::arithmetic` style). Trusted bodies
// (`external_body`); their `#[requires]` is CHECKED at every call site, so they
// cannot be misapplied. They feed `ay` the NIA facts it cannot derive itself.
// ---------------------------------------------------------------------------

/// AXIOM (right-multiplication monotonicity): `lo <= hi` and `f >= 0` imply
/// `lo*f <= hi*f`. Kernel content of `ay_certcut_scaling_sound`'s `k*A >= k*a`.
#[trust_vc::external_body]
#[trust_vc::requires(lo <= hi && f >= 0)]
#[trust_vc::ensures(lo * f <= hi * f)]
pub fn lemma_mul_le_mono_right(lo: int, hi: int, f: int) {}

/// AXIOM (commutativity): `q*d == d*q`.
#[trust_vc::external_body]
#[trust_vc::ensures(q * d == d * q)]
pub fn lemma_mul_comm(q: int, d: int) {}

/// AXIOM (right-distributivity over +1): `(q+1)*d == q*d + d`.
#[trust_vc::external_body]
#[trust_vc::ensures((q + 1) * d == q * d + d)]
pub fn lemma_mul_distrib_add1(q: int, d: int) {}

// ===========================================================================
// RULE 1 — ADD (impliedGe_add). At a fixed 0/1 point x, let `eval_a`/`eval_b` be
// the LHS values of the two operand constraints (`A`,`B`) and `rhs_a`/`rhs_b`
// their degrees. The recomputed sum constraint has degree `rhs_a + rhs_b`
// (refutation_check.rs:132 `out.rhs = self.rhs.checked_add(other.rhs)`) and LHS
// value `eval_a + eval_b` (the pointwise coeff merge). SOUNDNESS: if x satisfies
// A and B then x satisfies the sum. PROVES.
// ===========================================================================
#[trust_vc::ensures((eval_a >= rhs_a && eval_b >= rhs_b) ==> (result >= rhs_a + rhs_b))]
pub fn add_step_sound(eval_a: int, rhs_a: int, eval_b: int, rhs_b: int) -> int {
    eval_a + eval_b
}

/// NON-VACUITY CONTROL for ADD — claim the recomputed sum meets a degree ONE
/// HIGHER than `add` actually produces (`rhs_a + rhs_b + 1`). This is an
/// over-strong (unsound) bound, REFUTED with a counterexample (e.g. the operands
/// hold with equality).
#[trust_vc::ensures((eval_a >= rhs_a && eval_b >= rhs_b) ==> (result >= rhs_a + rhs_b + 1))]
pub fn add_step_overclaim(eval_a: int, rhs_a: int, eval_b: int, rhs_b: int) -> int {
    eval_a + eval_b
}

// ===========================================================================
// RULE 2 — SCALE (impliedGe_scale). The recomputed scaled constraint has degree
// `k * rhs_a` (refutation_check.rs:141) and LHS value `k * eval_a`. SOUNDNESS for
// the checker's side condition `k >= 1` (refutation_check.rs:138 rejects `k<1`):
// if x satisfies A (`eval_a >= rhs_a`) then `k*eval_a >= k*rhs_a`. PROVES via the
// monotonicity axiom (`rhs_a <= eval_a`, `k >= 0`).
// ===========================================================================
#[trust_vc::ensures((k >= 1 && eval_a >= rhs_a) ==> (result >= k * rhs_a))]
pub fn scale_step_sound_general(k: int, eval_a: int, rhs_a: int) -> int {
    if k >= 1 && eval_a >= rhs_a {
        // a <= s and k >= 0  =>  a*k <= s*k  (the scaling arrow's content).
        lemma_mul_le_mono_right(rhs_a, eval_a, k);
    }
    k * eval_a
}

/// NON-VACUITY CONTROL for SCALE (lemma is load-bearing) — the SAME body and
/// contract WITHOUT the monotonicity lemma call. `ay` cannot derive the nonlinear
/// `k*eval_a >= k*rhs_a` on its own, so this MUST NOT verify (returns a
/// non-`Verified` verdict). Demonstrates the proof of `scale_step_sound_general`
/// is not a vacuous NIA discharge.
#[trust_vc::ensures((k >= 1 && eval_a >= rhs_a) ==> (result >= k * rhs_a))]
pub fn scale_step_no_lemma(k: int, eval_a: int, rhs_a: int) -> int {
    k * eval_a
}

/// SCALE at the representative concrete multiplier `k = 2` (a fully LINEAR,
/// decidable instance of the rule): `eval_a >= rhs_a` implies `2*eval_a >=
/// 2*rhs_a`. PROVES with no axiom — the concrete-multiplier witness of the rule.
#[trust_vc::ensures((eval_a >= rhs_a) ==> (result >= 2 * rhs_a))]
pub fn scale_step_by2_sound(eval_a: int, rhs_a: int) -> int {
    2 * eval_a
}

/// NON-VACUITY CONTROL for SCALE (concrete) — overclaim `2*rhs_a + 1` on the
/// `k=2` scaled bound. REFUTED with a counterexample (the operand holds with
/// equality: `2*eval_a == 2*rhs_a < 2*rhs_a + 1`).
#[trust_vc::ensures((eval_a >= rhs_a) ==> (result >= 2 * rhs_a + 1))]
pub fn scale_step_by2_overclaim(eval_a: int, rhs_a: int) -> int {
    2 * eval_a
}

// ===========================================================================
// RULE 3 — DIVIDE (impliedGe_division). The soundness CRUX is that ceiling
// division ROUNDS UP: the divided degree `ceil(a/d)`, multiplied back by `d`,
// DOMINATES the original `a`. Over the integral 0/1 LHS this makes the divided
// constraint implied by the operand (with `x >= 0` and `ceil(c/d) >= c/d`). The
// kernel fact is `d * ceil_div(a,d) >= a` for `d >= 1`.
// ===========================================================================

/// `ceil_div` by the representative divisor `d = 2`, computed with the REAL
/// algorithm (refutation_check.rs:206-217) over the kernel's ℤ: i128 ->
/// `int`; `checked_div_euclid(2)?`/`checked_rem_euclid(2)?` -> `div_euclid(2)`/
/// `rem_euclid(2)` (the new trust-vc `div_euclid`/`rem_euclid`-on-`int`
/// capability built for this proof; the `Option`/`?` is i128 overflow fail-closed
/// plumbing — an accepted step never overflowed); `if d<1 { None }` -> the divisor
/// is the positive literal 2. PROVES `result * 2 >= a` (ceiling rounds up).
#[trust_vc::ensures(result * 2 >= a)]
pub fn ceil_div_by2_rounds_up(a: int) -> int {
    let q = a.div_euclid(2);
    let r = a.rem_euclid(2);
    if r == 0 {
        q
    } else {
        q + 1
    }
}

/// NON-VACUITY CONTROL for DIVIDE (concrete) — FLOOR division (`a.div_euclid(2)`,
/// dropping the `if r != 0 { q + 1 }` round-up). The floor UNDERSHOOTS: for odd
/// `a`, `floor(a/2)*2 = a - 1 < a`. REFUTED with a counterexample. An "overcounted
/// division coeff" / dropped round-up can therefore never pass the checker.
#[trust_vc::ensures(result * 2 >= a)]
pub fn floor_div_by2_wrong(a: int) -> int {
    a.div_euclid(2)
}

/// DIVIDE, GENERAL divisor `d >= 1`, ceiling rounds up — the `r != 0` case the
/// real `ceil_div` branches on (refutation_check.rs:212-216 else-arm `q+1`).
/// Stated from the Euclidean decomposition `a = d*q + r`, `0 <= r < d` that
/// `div_euclid`/`rem_euclid` GUARANTEE (the encoder's `int_euclidean_div`
/// soundness invariant), sidestepping `ay`'s symbolic-divisor div/mod boundary.
/// PROVES `result * d >= a` (`(q+1)*d = q*d + d = a - r + d > a` since `r < d`).
#[trust_vc::requires(d >= 1 && a == d * q + r && 1 <= r && r < d)]
#[trust_vc::ensures(result * d >= a)]
pub fn ceil_div_general_rem_pos(a: int, d: int, q: int, r: int) -> int {
    lemma_mul_comm(q, d);
    lemma_mul_distrib_add1(q, d);
    q + 1
}

/// DIVIDE, GENERAL divisor, the exact-division case `r == 0` the real `ceil_div`
/// branches on (refutation_check.rs:213 then-arm `q`). PROVES `result * d >= a`
/// (here `q*d = d*q = a`).
#[trust_vc::requires(d >= 1 && a == d * q + r && r == 0)]
#[trust_vc::ensures(result * d >= a)]
pub fn ceil_div_general_rem_zero(a: int, d: int, q: int, r: int) -> int {
    lemma_mul_comm(q, d);
    q
}

/// NON-VACUITY CONTROL for DIVIDE (general) — FLOOR (`q`) in the `r != 0` case.
/// `floor(a/d)*d = a - r < a` since `r >= 1`. REFUTED with a counterexample.
#[trust_vc::requires(d >= 1 && a == d * q + r && 1 <= r && r < d)]
#[trust_vc::ensures(result * d >= a)]
pub fn floor_div_general_wrong(a: int, d: int, q: int, r: int) -> int {
    lemma_mul_comm(q, d);
    q
}

// ===========================================================================
// RULE 4 — WEAKEN (rhs order, `ay_certcut_rhs_weaken_sound`). A `>=` fact may be
// weakened to any smaller degree: if `rhs_lo <= rhs_hi` and x satisfies the
// stronger bound (`eval >= rhs_hi`) then it satisfies the weaker (`eval >=
// rhs_lo`). Underpins the division/aggregation builders' degree handling. PROVES.
// ===========================================================================
#[trust_vc::ensures((rhs_lo <= rhs_hi && eval >= rhs_hi) ==> (eval >= rhs_lo))]
pub fn weaken_step_sound(eval: int, rhs_hi: int, rhs_lo: int) -> int {
    eval
}

// ===========================================================================
// TERMINAL — CONTRADICTION (pb_unsat_of_contradictory_bounds,
// refutation_check.rs:183-185). The checker accepts a refutation only when the
// final constraint is `0 >= c` with `c >= 1` (`is_contradiction`). An empty-LHS
// constraint evaluates to `0` at EVERY 0/1 point, so `c >= 1` makes `0 >= c`
// UNSATISFIABLE — the refutation is genuine. PROVES `c>=1 ==> !(0 >= c)`.
// ===========================================================================
#[trust_vc::ensures(rhs >= 1 ==> !(0 >= rhs))]
pub fn contradiction_terminal_unsat(rhs: int) -> bool {
    rhs >= 1
}

/// NON-VACUITY CONTROL for TERMINAL — accept the weaker bound `c >= 0`. But
/// `0 >= 0` IS satisfiable (the empty LHS attains it), so `c >= 0` is NOT a
/// contradiction. REFUTED with a counterexample (`c = 0`). Pins that the
/// checker's `rhs >= 1` threshold (not `>= 0`) is the sound one.
#[trust_vc::ensures(rhs >= 0 ==> !(0 >= rhs))]
pub fn contradiction_terminal_wrong(rhs: int) -> bool {
    rhs >= 0
}
