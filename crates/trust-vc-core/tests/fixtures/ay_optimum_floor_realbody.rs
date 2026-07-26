// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// =====================================================================
// NON-VACUOUS native-deductive proof that the in-production cutting-planes
// OPTIMUM SELF-CHECK (`crates/ay-pb/src/proof/optimum_check.rs`) CERTIFIES
// ONLY SOUND LOWER BOUNDS — a floor `F` that `check_floor` accepts is a
// TRUE lower bound on the objective over the whole feasible region, and the
// `certify_optimum` tightness gate promotes to OPTIMUM only at `F == UB`.
// Matches the kernel duals `cut_lower_bound_is_sound_floor` /
// `pb_optimum_eq_of_cut_lower_bound` in
// `proofs/clean-pb/PBCertificateAlgebra.lean`. Discharged by trust-vc on the
// pure-Rust `ay` SMT solver, kernel-rechecked.
// =====================================================================
//
// WHAT "certifies only sound lower bounds" MEANS HERE
// --------------------------------------------------
// `ObjectiveBound::check_floor` (optimum_check.rs:90-110) replays the
// cutting-planes derivation (`replay_derivation`, the SAME kernel arrows whose
// per-step soundness is proven in `refutation_step_realbody.rs`) and accepts the
// claimed floor `F` IFF the derived constraint is IDENTICAL to the objective form
// at degree `F` (`derived == target`: same per-variable coefficients AND
// `derived.rhs == claimed_floor`). Because every replayed step is entailment-
// preserving (the refutation-step proof), the derived constraint holds at every
// feasible point; the equality check then transports that bound onto the EXACT
// objective form, so for every feasible `x`: `objective(x) == eval(derived,x) >=
// derived.rhs == F`. This fixture PROVES that terminal transport (the dual of the
// refutation `0 >= 1` terminal), the `var_geq_zero` LIFT step the cert builders
// use, and the `certify_optimum` tightness gate — each at the per-point /
// scalar level, the soundness crux. The replay loop itself is the whole-loop
// boundary; its per-step content is the sibling refutation-step proof.
//
// `int` (Verus ℤ) AND the `lemma_*` AXIOM: identical rationale to
// `refutation_step_realbody.rs` — the i128 checker's `checked_*` ops reject any
// overflowing step (so accepted arithmetic is exact ℤ), and `ay`'s NIA
// incompleteness on the lift product `k*x` is closed by the CHECKED-precondition
// multiplication-monotonicity axiom.
//
// HOW THIS IS VERIFIED: `trust_vc_core::verify_function_from_file(<this file>,
// <fn>)`. `Verified` == ay UNSAT + trust-vc-kernel accepted; `Counterexample` ==
// ay returned a concrete falsifying model.

// =====================================================================
// VERBATIM real checker source (copied from crates/ay-pb/src/proof/
// optimum_check.rs and refutation_check.rs; a later step diff-checks these
// blocks against the live source). The soundness LEMMAS below mirror them.
// =====================================================================
//
// --- ObjectiveBound::check_floor (optimum_check.rs:90-110) ---
//   pub fn check_floor(&self) -> Result<i128, OptError> {
//       let target = pb_ge(&PbConstraint {
//           terms: self.objective_terms.clone(),
//           rel: PbRel::Ge,
//           rhs: self.claimed_floor,
//       })
//       .ok_or(OptError::UnmodeledObjective)?;
//       let derived = replay_derivation(&self.inputs, &self.steps).map_err(OptError::Replay)?;
//       // The derived constraint must be IDENTICAL to the objective floor: same
//       // per-variable coefficients AND the same RHS. Equality (not `>=`) is the
//       // dual of the refutation checker's `0 >= c` terminal: a builder that
//       // claims a floor the derivation does not actually reach is rejected.
//       if derived == target {
//           Ok(self.claimed_floor)
//       } else {
//           Err(OptError::NotObjectiveFloor)
//       }
//   }
//
// --- ObjectiveBound::certify_optimum (optimum_check.rs:120-127) ---
//   pub fn certify_optimum(&self, incumbent_value: i128) -> Result<i128, OptError> {
//       let floor = self.check_floor()?;
//       if incumbent_value == floor {
//           Ok(floor)
//       } else {
//           Err(OptError::NotTight)
//       }
//   }
//
// --- LinConstraint::var_geq_zero (refutation_check.rs:197-201) — the LIFT axiom ---
//   pub(crate) fn var_geq_zero(var: u32) -> Self {
//       let mut out = Self::constant(0);
//       out.coeff.insert(var, 1);
//       out
//   }
//
// --- aggregation LIFT step (build_aggregation_floor_cert, optimum_check.rs:293-314) ---
//   // 4. LIFT each objective variable up to its objective coefficient.
//   for &v in &obj_vars {
//       let have = coeff_after(v)?;
//       let want = *objc.get(&v)?;
//       let lift = want.checked_sub(have)?;
//       if lift < 0 {
//           return None; // unsound shape (should not happen by the M bound)
//       }
//       if lift == 0 {
//           continue;
//       }
//       let axiom_idx = *axiom_index.get(&v)?;
//       if lift == 1 {
//           steps.push(RefStep::Add(cur, axiom_idx));
//       } else {
//           // scale the x_v>=0 axiom by `lift`, then add.
//           steps.push(RefStep::Scale(axiom_idx, lift));
//           let scaled_idx = inputs.len() + steps.len() - 1;
//           steps.push(RefStep::Add(cur, scaled_idx));
//       }
//       cur = inputs.len() + steps.len() - 1;
//   }
// =====================================================================

/// AXIOM (right-multiplication monotonicity), as in `refutation_step_realbody.rs`.
/// Trusted body; `#[requires]` CHECKED at every call site. Closes the lift's NIA.
#[trust_vc::external_body]
#[trust_vc::requires(lo <= hi && f >= 0)]
#[trust_vc::ensures(lo * f <= hi * f)]
pub fn lemma_mul_le_mono_right(lo: int, hi: int, f: int) {}

// ===========================================================================
// TERMINAL — check_floor's `derived == target` transport (the dual of the
// refutation `0 >= 1`). At a fixed feasible point x: `eval_derived` is the LHS
// value of the replayed derived constraint, `derived_rhs` its degree, `eval_obj`
// the objective value. The derived constraint is entailment-sound (proved in
// `refutation_step_realbody.rs`), so `eval_derived >= derived_rhs` (the
// `#[requires]`). The acceptance condition `derived == target` gives same
// coefficients (`eval_derived == eval_obj` at x) AND `derived_rhs ==
// claimed_floor`. CONCLUSION: `eval_obj >= claimed_floor` — `F` is a TRUE floor
// on the objective. PROVES.
// ===========================================================================
#[trust_vc::requires(eval_derived >= derived_rhs)]
#[trust_vc::ensures(
    (eval_derived == eval_obj && derived_rhs == claimed_floor) ==> (eval_obj >= claimed_floor)
)]
pub fn check_floor_terminal_sound(
    eval_derived: int,
    derived_rhs: int,
    eval_obj: int,
    claimed_floor: int,
) -> bool {
    eval_derived == eval_obj && derived_rhs == claimed_floor
}

/// NON-VACUITY CONTROL — WRONG OBJECTIVE FORM: drop the coefficient-equality half
/// of `derived == target` (accept a bound on a DIFFERENT linear form). The
/// derived bound then says nothing about THIS objective: REFUTED with a
/// counterexample (`eval_derived >= F` but `eval_obj < F`). Mirrors
/// `negative_control_wrong_objective_form_is_rejected` (optimum_check.rs:920).
#[trust_vc::requires(eval_derived >= derived_rhs)]
#[trust_vc::ensures((derived_rhs == claimed_floor) ==> (eval_obj >= claimed_floor))]
pub fn check_floor_wrong_form(
    eval_derived: int,
    derived_rhs: int,
    eval_obj: int,
    claimed_floor: int,
) -> bool {
    derived_rhs == claimed_floor
}

/// NON-VACUITY CONTROL — OVERCOUNTED FLOOR: replace the checker's `derived.rhs ==
/// claimed_floor` by the unsound `claimed_floor >= derived.rhs` (certify a floor
/// AT OR ABOVE the degree the derivation actually reaches). REFUTED with a
/// counterexample (`claimed_floor > derived_rhs == eval_obj`). Mirrors
/// `negative_control_overcounted_floor_is_rejected` (optimum_check.rs:904): an
/// overcounted lower bound can NEVER yield a wrong OPTIMUM.
#[trust_vc::requires(eval_derived >= derived_rhs)]
#[trust_vc::ensures(
    (eval_derived == eval_obj && claimed_floor >= derived_rhs) ==> (eval_obj >= claimed_floor)
)]
pub fn check_floor_overcount_wrong(
    eval_derived: int,
    derived_rhs: int,
    eval_obj: int,
    claimed_floor: int,
) -> bool {
    eval_derived == eval_obj && claimed_floor >= derived_rhs
}

// ===========================================================================
// LIFT — var_geq_zero soundness (refutation_check.rs:197-201; used at
// build_aggregation_floor_cert:293-314 and build_covering_floor_cert:450-470).
// The builder raises a coefficient to its objective value by ADDING
// `lift * (x_v >= 0)`. At a 0/1 point `x_v >= 0`, and `lift >= 0` (the builder's
// `if lift < 0 { return None }` guard), so the added term `lift * x_v >= 0`:
// adding it never lowers the constraint's LHS, so the floor is preserved. PROVES
// `lift * x_v >= 0`.
// ===========================================================================
#[trust_vc::ensures((xv >= 0 && lift >= 0) ==> (result >= 0))]
pub fn lift_var_geq_zero_sound(xv: int, lift: int) -> int {
    if xv >= 0 && lift >= 0 {
        // 0 <= xv and lift >= 0  =>  0*lift <= xv*lift  =>  0 <= lift*xv.
        lemma_mul_le_mono_right(0, xv, lift);
    }
    lift * xv
}

/// NON-VACUITY CONTROL for LIFT (lemma is load-bearing) — same body/contract with
/// NO monotonicity lemma. `ay` cannot derive the nonlinear `lift*xv >= 0`, so this
/// MUST NOT verify (non-`Verified`).
#[trust_vc::ensures((xv >= 0 && lift >= 0) ==> (result >= 0))]
pub fn lift_var_geq_zero_no_lemma(xv: int, lift: int) -> int {
    lift * xv
}

// ===========================================================================
// TIGHTNESS GATE — certify_optimum (optimum_check.rs:120-127). Given a CHECKED
// floor `F` (`check_floor` above: every feasible x has `obj_x >= F`, the
// `#[requires]`) and a VIG-verified incumbent attaining `incumbent`, the gate
// returns `Ok(F)` IFF `incumbent == F`. SOUNDNESS: when it fires, `incumbent ==
// F <= obj_x` for every feasible x, so the incumbent is OPTIMAL (no feasible
// point beats it). PROVES `incumbent == floor ==> obj_x >= incumbent`.
// ===========================================================================
#[trust_vc::requires(obj_x >= floor)]
#[trust_vc::ensures((incumbent == floor) ==> (obj_x >= incumbent))]
pub fn certify_optimum_tightness_sound(obj_x: int, floor: int, incumbent: int) -> bool {
    incumbent == floor
}

/// NON-VACUITY CONTROL — DROP TIGHTNESS: promote to OPTIMUM regardless of
/// `incumbent == floor`. Unsound when `incumbent > floor` (the floor is only a
/// bound, not attained), so it would declare a non-optimal incumbent optimal.
/// REFUTED with a counterexample (`floor <= obj_x < incumbent`). Mirrors
/// `negative_control_floor_below_incumbent_is_not_optimum` (optimum_check.rs:935).
#[trust_vc::requires(obj_x >= floor)]
#[trust_vc::ensures(obj_x >= incumbent)]
pub fn certify_optimum_drop_tightness(obj_x: int, floor: int, incumbent: int) -> bool {
    incumbent == floor
}
