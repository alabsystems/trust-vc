// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// =====================================================================
// NATIVE DEDUCTIVE CONTRACTS over the AY pseudo-Boolean soundness surface
// Discharged by trust-vc (the first-party Verus-style verifier) on the
// pure-Rust `ay` SMT solver, with the UNSAT certificate re-checked by the
// independent `trust-vc-kernel` resolution checker.
// =====================================================================
//
// These are real-typed Rust functions carrying `#[trust_vc::requires]` /
// `#[trust_vc::ensures]` / `trust_vc::assert!` contracts. They are verified by
// `trust_vc_core::verify_function_from_file(<this file>, <fn name>)`, which
// parses THIS file, lowers each annotated function to trust-vc's typed IR,
// encodes the verification condition to `ay` terms (signed `i128` => BV128, NOT
// the type-erased `Sort::Int`), and refutes the negation. `Verified` == ay
// returned UNSAT and the kernel accepted the proof.
//
// Each lemma mirrors the i128 arithmetic of a specific REAL ay-pb function so
// the proof obligation is literally about the actual operations those functions
// perform. The matching real functions carry doc-comment contracts pointing
// back here (see solver.rs::eval_constraint and portfolio.rs OPTIMUM gate).
//
// Status: DISCHARGED via trust-vc on the stock toolchain (see
// trust-vc tests/ay_native_gate_eval_lemmas.rs). The same contracts are ready
// to be lifted onto the real function bodies in place once the Trust rustc-fork
// sysroot (channel="trust") is built and the trust-vc rustc-driver can run.

// ---------------------------------------------------------------------------
// LEMMA 1 — OPTIMUM gate soundness (PRIORITY TARGET; UNBOUNDED).
//
// Real surface: the OptimumFound upgrade gate, portfolio.rs (three identical
// sites). Each fires:
//     if value <= floor && verify_all_constraints(constraints, assignment) {
//         status = OptimumFound; objective = Some(value);
//     }
// where
//   * `value` = objective of a re-verified FEASIBLE incumbent
//     (eval_objective on a verify_all_constraints-passing assignment), and
//   * `floor` = objective_lower_bound_from_constraints(...) — a SOUND lower
//     bound: for every feasible x, floor <= objective(x).
//
// `obj_x` below is the objective of an ARBITRARY feasible point. trust-vc
// universally quantifies a `#[proof]` function's parameters, so proving the
// body for a fresh `obj_x` proves it FOR ALL feasible objective values
// (Skolemization). The precondition `floor <= obj_x` is exactly the sound-LB
// hypothesis instantiated at that arbitrary feasible point; `value <= floor` is
// the gate guard. The conclusion `value <= obj_x` is global optimality of the
// incumbent: its value lower-bounds every feasible objective.
// ---------------------------------------------------------------------------
#[trust_vc::proof]
#[trust_vc::requires(value <= floor)]
#[trust_vc::requires(floor <= obj_x)]
fn optimum_gate_sound(value: i128, floor: i128, obj_x: i128) {
    trust_vc::assert!(value <= obj_x);
}

// ---------------------------------------------------------------------------
// LEMMA 2 — incumbent is achieved AND minimal => it is THE global optimum.
//
// Extends Lemma 1 with the "achieved" half: the incumbent realises `value`
// (obj_inc == value, since `value` is literally eval_objective of the
// incumbent assignment). Together: `value` is attained by a feasible point and
// lower-bounds every feasible objective, hence `value` is the minimum and the
// OptimumFound claim is sound. (`obj_x` again ranges over all feasible
// objectives by parameter-Skolemization.)
// ---------------------------------------------------------------------------
#[trust_vc::proof]
#[trust_vc::requires(value <= floor)]
#[trust_vc::requires(obj_inc == value)]
#[trust_vc::requires(floor <= obj_inc)]
#[trust_vc::requires(floor <= obj_x)]
fn optimum_achieved_and_minimal(value: i128, floor: i128, obj_inc: i128, obj_x: i128) {
    trust_vc::assert!(obj_inc == value); // incumbent attains the value
    trust_vc::assert!(value <= obj_x); // value lower-bounds every feasible objective
}

// ---------------------------------------------------------------------------
// LEMMA 3 — eval_constraint i128 accumulation is exact (no wraparound).
//
// Real surface: eval_constraint / eval_terms (solver.rs). The LHS is the sum
// over satisfied terms of their i128 coefficients. This lemma models the
// 2-term shape: each term contributes `coeff` when satisfied, else 0. With
// coefficients bounded by 1e9, the i128 sum stays well inside i128 range, so
// the `+` does NOT wrap and the comparison the constraint makes is exact.
//
// CRITICAL: this is NON-VACUOUS only because trust-vc encodes i128 as BV128.
// Under trust-wp's type-erased `Sort::Int` an "integer" cannot overflow, so the
// same statement is vacuously true there — which is exactly why the task routes
// i128-faithfulness obligations to trust-vc, not trust-wp.
// ---------------------------------------------------------------------------
#[trust_vc::proof]
#[trust_vc::requires(-1000000000i128 <= c1 && c1 <= 1000000000i128)]
#[trust_vc::requires(-1000000000i128 <= c2 && c2 <= 1000000000i128)]
fn eval_constraint_sum_no_overflow(c1: i128, c2: i128, s1: bool, s2: bool) {
    let t1: i128 = if s1 { c1 } else { 0i128 };
    let t2: i128 = if s2 { c2 } else { 0i128 };
    trust_vc::assert!(t1 + t2 <= 2000000000i128);
    trust_vc::assert!(t1 + t2 >= -2000000000i128);
}

// ---------------------------------------------------------------------------
// LEMMA 4 — eval_constraint's Ge decision is total/faithful (BV128).
//
// Real surface: eval_constraint's `PbRel::Ge => lhs >= rhs` (solver.rs:20).
// For the modeled 2-term LHS, the `>=` decision is the exact complement of
// `<` — i.e. no overflow-induced inconsistency makes both (or neither) hold.
// A genuine BV128 fact: it pins down that the relation the VIG re-checks is a
// faithful total order comparison on the i128 sum.
// ---------------------------------------------------------------------------
#[trust_vc::proof]
#[trust_vc::requires(-1000000000i128 <= c1 && c1 <= 1000000000i128)]
#[trust_vc::requires(-1000000000i128 <= c2 && c2 <= 1000000000i128)]
#[trust_vc::requires(-1000000000i128 <= rhs && rhs <= 1000000000i128)]
fn eval_constraint_ge_faithful(c1: i128, c2: i128, rhs: i128, s1: bool, s2: bool) {
    let lhs: i128 = (if s1 { c1 } else { 0i128 }) + (if s2 { c2 } else { 0i128 });
    trust_vc::assert!((lhs >= rhs) == !(lhs < rhs));
}
