// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Int-mode arithmetic encoding.

use ay_dpll::api::Term;

use crate::encoder::arith_semantics::resolve_expr_wrap;
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{ArithOp, TrustVcType};

/// Verus's `/` and `%` on the unbounded `int` / `nat` sorts are *Euclidean*:
/// the quotient rounds toward -inf and the remainder is always non-negative
/// (`q*b + r == a`, `0 <= r < |b|`). Finite-width Rust integers, by contrast,
/// truncate toward zero. This predicate selects the Euclidean encoding for the
/// mathematical-integer sorts only, so Rust finite-width `/`/`%` stay truncated
/// (#2778).
fn is_math_integer(ty: &TrustVcType) -> bool {
    matches!(ty, TrustVcType::MathInt | TrustVcType::Nat)
}

impl<'a> AstExpressionParser<'a> {
    /// Encode arithmetic in Int mode (#2036, #2046).
    #[allow(clippy::too_many_arguments)]
    pub(in crate::encoder::ir_encoder) fn encode_int_arith(
        &mut self,
        op: ArithOp,
        left: Term,
        right: Term,
        right_is_zero: bool,
        right_is_one: bool,
        ty: &TrustVcType,
        divisor_literal: Option<i128>,
    ) -> TrustVcResult<Term> {
        // Per-expression type > quantifier scope (#2046, shared arith_semantics).
        // When use_int_arithmetic is true (termination proofs / measure mode),
        // all variables are Sort::Int and arithmetic must be pure math — no
        // modular wrapping. The TrustVcExpr still carries the original BV type
        // (e.g., Int{64}) but the solver operates on unbounded integers.
        // Wrapping is only needed in quantifier-body int_mode where BV semantics
        // must be preserved. Fixes typed-path regression for loop_decreases.
        let scope_sem = self.current_quantifier_wrap_semantics();
        let wrap_ctx = if self.use_int_arithmetic {
            None
        } else {
            resolve_expr_wrap(ty, scope_sem)
        };

        // Quantifier bodies are SPEC arithmetic, and spec arithmetic on `uN`/`iN`
        // is MATHEMATICAL — Verus lowers `i + 1` on a `u64` binder to unbounded
        // `int` addition; there is no modulus and no overflow.
        //
        // Wrapping a quantifier body was a CARDINAL FALSE VERIFY, because the
        // overflow obligation that would have caught the wrap is *structurally*
        // unavailable here: the predicate would reference the bound variable,
        // which becomes free at the outer assertion scope (#2557), so every
        // `quantifier_depth == 0` guard below suppresses it. The body therefore
        // got neither faithful semantics nor a check, and
        //   `forall|i: u64| i + 1 <= u64::MAX`   (false: i = MAX)
        //   `forall|i: i8|  0 - i <= 127`        (false: i = i8::MIN)
        //   `exists|i: i8|  i + 1 == -128`       (false)
        // all reported `verified`, while the TRUE `forall|i: u64| i + 1 > i` was
        // refuted. Declining the wrap fixes both directions at once.
        //
        // This does NOT under-constrain: `build_range_guards` still pins each
        // binder to its own type's range (`0 <= i < 2^64` for `u64`), so the
        // binder stays a `u64`-valued Int — only the RESULT of the body's
        // arithmetic is unbounded, exactly as in Verus.
        //
        // Scope pins:
        //  * `Div`/`Rem` keep `wrap_ctx`: it is not a wrap there, it selects the
        //    signed MIN/-1 "undefined" guard (#1873), which stays.
        //  * Explicit `wrapping_*`/`checked_*`/`saturating_*` (`WrappingArith`)
        //    are DEFINED as finite-width and keep truncating — `encode_int_checked`
        //    / `encode_int_saturating` compute their own wrap context, and the
        //    `Wrapping` arm in `wrapping.rs` now applies the type-derived wrap
        //    itself instead of relying on this one.
        //  * Outside a quantifier (`quantifier_depth == 0`) nothing changes; the
        //    machine-semantics BV path and its obligations are untouched.
        let arith_wrap_ctx = if self.quantifier_depth > 0 {
            None
        } else {
            wrap_ctx
        };

        match op {
            ArithOp::Add => {
                let result = self
                    .solver
                    .try_add(left, right)
                    .map_err(|e| e.to_string())?;
                let wrapped = self.wrap_int_with_ctx(result, arith_wrap_ctx)?;
                // Guard: only collect overflow predicates at quantifier_depth==0.
                // Inside quantifier bodies, the predicate references bound variables;
                // asserting it at the outer scope constrains those variables globally,
                // causing false Verified results. Part of #2557.
                if self.overflow_behavior.should_check()
                    && wrap_ctx.is_some()
                    && !right_is_zero
                    && self.quantifier_depth == 0
                {
                    if let Some(no_overflow) =
                        self.int_result_in_wrap_range_ctx(result, wrap_ctx)?
                    {
                        self.overflow_checks
                            .push(("int addition overflow".into(), no_overflow));
                    }
                }
                Ok(wrapped)
            }
            ArithOp::Sub => {
                let result = self
                    .solver
                    .try_sub(left, right)
                    .map_err(|e| e.to_string())?;
                let wrapped = self.wrap_int_with_ctx(result, arith_wrap_ctx)?;
                if self.overflow_behavior.should_check()
                    && wrap_ctx.is_some()
                    && !right_is_zero
                    && self.quantifier_depth == 0
                {
                    if let Some(no_overflow) =
                        self.int_result_in_wrap_range_ctx(result, wrap_ctx)?
                    {
                        self.overflow_checks
                            .push(("int subtraction overflow".into(), no_overflow));
                    }
                }
                Ok(wrapped)
            }
            ArithOp::Mul => {
                let result = self
                    .solver
                    .try_mul(left, right)
                    .map_err(|e| e.to_string())?;
                let wrapped = self.wrap_int_with_ctx(result, arith_wrap_ctx)?;
                if self.overflow_behavior.should_check()
                    && wrap_ctx.is_some()
                    && !right_is_zero
                    && !right_is_one
                    && self.quantifier_depth == 0
                {
                    if let Some(no_overflow) =
                        self.int_result_in_wrap_range_ctx(result, wrap_ctx)?
                    {
                        self.overflow_checks
                            .push(("int multiplication overflow".into(), no_overflow));
                    }
                }
                Ok(wrapped)
            }
            ArithOp::Div => {
                if right_is_zero {
                    return Err("Division by zero: divisor is constant 0".to_string().into());
                }
                if self.overflow_behavior.should_check() && self.quantifier_depth == 0 {
                    // At depth 0, push overflow predicates to the outer scope.
                    let zero = self.solver.int_const(0);
                    let eq_zero = self.solver.try_eq(right, zero).map_err(|e| e.to_string())?;
                    let not_zero = self.solver.try_not(eq_zero).map_err(|e| e.to_string())?;
                    self.overflow_checks
                        .push(("division by zero".into(), not_zero));
                    if let Some(no_overflow) =
                        self.int_mode_signed_div_rem_no_overflow_ctx(left, right, wrap_ctx)
                    {
                        self.overflow_checks
                            .push(("signed division MIN/-1 overflow".into(), no_overflow));
                    }
                }
                // Verus `int`/`nat` division is Euclidean (rounds toward -inf,
                // non-negative remainder), unlike Rust finite-width truncating
                // `/`. The mathematical-integer sorts have no finite MIN, so the
                // signed MIN/-1 undefined guard below never applies — return the
                // Euclidean quotient directly. #2778.
                if is_math_integer(ty) {
                    // Division by a LITERAL constant divisor is decidable LIA+div:
                    // purify to fresh quotient/remainder vars constrained by the
                    // exact Euclidean axioms, keeping the query out of ay's
                    // unsupported symbolic-div/mod fragment (#2778).
                    if let Some(d) = self.euclidean_literal_divisor(divisor_literal) {
                        let (q, _r) = self.purified_euclidean_div_mod_literal(left, d)?;
                        return Ok(q);
                    }
                    // SYMBOLIC divisor at the outer scope: encode as the
                    // `__euclid!div` UF application under the divisor-guarded
                    // Euclidean lemma instances (#2778 — nonlinear.rs test4).
                    // Inside quantifier bodies keep the native term (ay
                    // fail-closes to Unknown there; asserting the ground
                    // lemmas would reference bound variables).
                    if self.quantifier_depth == 0 && !self.pending_universal_closure {
                        let (q, _r) = self.guarded_euclidean_div_mod_symbolic(left, right)?;
                        return Ok(q);
                    }
                    return self.int_euclidean_div(left, right);
                }
                let result = self.int_truncation_div(left, right)?;
                // Inside quantifier bodies (depth > 0), Rust's unconditional
                // panic on signed MIN/-1 must be modeled as undefined. This is
                // NOT gated by overflow_behavior: MIN/-1 panics in both debug
                // and release Rust, unlike add/sub/mul overflow which only
                // panics in debug. Replace result with a fresh unconstrained
                // variable when the overflow condition is met. #1873.
                if self.quantifier_depth > 0 {
                    if let Some(guarded) = self
                        .int_div_rem_overflow_as_undefined(left, right, result, wrap_ctx, "div")?
                    {
                        return Ok(guarded);
                    }
                }
                Ok(result)
            }
            ArithOp::Rem => {
                if right_is_zero {
                    return Err("Modulo by zero: divisor is constant 0".to_string().into());
                }
                if self.overflow_behavior.should_check() && self.quantifier_depth == 0 {
                    let zero = self.solver.int_const(0);
                    let eq_zero = self.solver.try_eq(right, zero).map_err(|e| e.to_string())?;
                    let not_zero = self.solver.try_not(eq_zero).map_err(|e| e.to_string())?;
                    self.overflow_checks
                        .push(("modulo by zero".into(), not_zero));
                    if let Some(no_overflow) =
                        self.int_mode_signed_div_rem_no_overflow_ctx(left, right, wrap_ctx)
                    {
                        self.overflow_checks
                            .push(("signed remainder MIN/-1 overflow".into(), no_overflow));
                    }
                }
                // Euclidean (non-negative) remainder for the unbounded `int`/
                // `nat` sorts; finite-width Rust `%` stays truncated below. #2778.
                if is_math_integer(ty) {
                    // Remainder by a LITERAL constant divisor: same purification as
                    // the Div arm — fresh remainder var under the Euclidean axioms,
                    // decidable LIA+div (#2778).
                    if let Some(d) = self.euclidean_literal_divisor(divisor_literal) {
                        let (_q, r) = self.purified_euclidean_div_mod_literal(left, d)?;
                        return Ok(r);
                    }
                    // SYMBOLIC divisor: same guarded UF encoding as the Div
                    // arm (#2778).
                    if self.quantifier_depth == 0 && !self.pending_universal_closure {
                        let (_q, r) = self.guarded_euclidean_div_mod_symbolic(left, right)?;
                        return Ok(r);
                    }
                    return self.int_euclidean_mod(left, right);
                }
                let result = self.int_truncation_rem(left, right)?;
                // Same unconditional depth > 0 guard as Div. #1873.
                if self.quantifier_depth > 0 {
                    if let Some(guarded) = self
                        .int_div_rem_overflow_as_undefined(left, right, result, wrap_ctx, "rem")?
                    {
                        return Ok(guarded);
                    }
                }
                Ok(result)
            }
        }
    }

    /// Soundness gate for Euclidean div/mod-by-constant purification (#2778).
    ///
    /// Returns the literal divisor `d` only when purification is BOTH sound and
    /// beneficial:
    /// * `divisor_literal` is `Some(d)` — the divisor is a compile-time constant
    ///   (a symbolic divisor stays `None` and is left on the native path, where
    ///   ay soundly returns `Unknown`: genuinely nonlinear, fail-closed);
    /// * `d != 0` — a zero divisor is already rejected by the caller;
    /// * `self.quantifier_depth == 0` — the defining axioms are asserted at the
    ///   outer solver scope, so the dividend must be free of enclosing bound
    ///   variables. Inside a quantifier body the dividend may reference bound
    ///   variables, and globally asserting `dividend == q*d + r` would unsoundly
    ///   constrain them; there we fall back to the native Euclidean term
    ///   (status quo). This mirrors the `quantifier_depth == 0` gate already used
    ///   for overflow side-checks.
    fn euclidean_literal_divisor(&self, divisor_literal: Option<i128>) -> Option<i128> {
        // BINDER CAPTURE (CARDINAL), same root cause as
        // `bind_datatype_match_result`: `purified_euclidean_div_mod_literal`
        // hoists `dividend == q*d + r` to the SOLVER TOP LEVEL. That is only
        // sound while `dividend`'s free variables are themselves top level.
        // `add_typed_broadcast` encodes a spec-fn body BEFORE closing its
        // `forall`, so `quantifier_depth` is 0 there even though a binder IS
        // coming — the hoisted definition keeps the free constant while the
        // axiom's occurrence gets bound, and the axiom degenerates to
        // `forall n. f(n) == __euclid_q`. Combined with the ground replay of
        // the same body it makes the whole context INCONSISTENT (measured:
        // `fn half(n: int) -> int { n / 2 }` verifies `half(2) == 5`).
        if self.quantifier_depth != 0 || self.pending_universal_closure {
            return None;
        }
        match divisor_literal {
            Some(d) if d != 0 => Some(d),
            _ => None,
        }
    }

    /// Purified Euclidean div/mod for a LITERAL constant divisor `d != 0`.
    ///
    /// Introduces fresh quotient `q` and remainder `r` constrained by the exact
    /// SMT-LIB Euclidean axioms
    /// `dividend == q*d + r` and `0 <= r < |d|`,
    /// then returns `(q, r)`. Because `d` is a constant the product `q*d` is
    /// *linear*, so the whole obligation stays inside decidable LIA — the native
    /// `(div a d)` / `(mod a d)` terms (which ay leaves in its unsupported
    /// symbolic-div/mod fragment and reports `Unknown` for) are never emitted.
    ///
    /// SOUNDNESS: the two axioms are precisely the SMT-LIB Euclidean definition
    /// of `div`/`mod` (quotient rounds toward -inf, non-negative remainder), the
    /// same semantics as [`int_euclidean_div`](Self::int_euclidean_div). For any
    /// fixed dividend value and any `d != 0` they pin `q` and `r` UNIQUELY, so
    /// this is a faithful *definition*, not an over-approximation: it can neither
    /// invent a value the native term could not take nor drop one it could. The
    /// caller guarantees `d != 0` and `quantifier_depth == 0`
    /// (see [`euclidean_literal_divisor`](Self::euclidean_literal_divisor)).
    ///
    /// The `(q, r)` pair is memoized by `(dividend, d)` so that `a / d` and
    /// `a % d` (and any repeated occurrence) resolve to the SAME quotient and
    /// remainder. Sharing is what keeps the query decidable: distinct fresh
    /// pairs would oblige the solver to re-prove remainder uniqueness, which ay
    /// reports `Unknown` for even though it is LIA-valid.
    fn purified_euclidean_div_mod_literal(
        &mut self,
        dividend: Term,
        d: i128,
    ) -> TrustVcResult<(Term, Term)> {
        use ay_dpll::api::Sort;
        use num_bigint::BigInt;

        debug_assert!(
            d != 0,
            "purified Euclidean div/mod requires a non-zero divisor"
        );

        if let Some(&pair) = self.euclid_div_mod_aliases.get(&(dividend, d)) {
            return Ok(pair);
        }

        let q = self.solver.fresh_var("__euclid_q", Sort::Int);
        let r = self.solver.fresh_var("__euclid_r", Sort::Int);

        // dividend == q*d + r   (q*d is linear: multiplication by the constant d)
        let d_term = self.solver.int_const_bigint(&BigInt::from(d));
        let qd = self.solver.try_mul(q, d_term).map_err(|e| e.to_string())?;
        let recon = self.solver.try_add(qd, r).map_err(|e| e.to_string())?;
        let def = self
            .solver
            .try_eq(recon, dividend)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(def)
            .map_err(|e| format!("Failed to assert Euclidean div/mod definition: {e}"))?;

        // 0 <= r
        let zero = self.solver.int_const(0);
        let r_nonneg = self.solver.try_ge(r, zero).map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(r_nonneg)
            .map_err(|e| format!("Failed to assert Euclidean remainder lower bound: {e}"))?;

        // r < |d|
        let abs_d = BigInt::from(d.unsigned_abs());
        let abs_d_term = self.solver.int_const_bigint(&abs_d);
        let r_lt = self
            .solver
            .try_lt(r, abs_d_term)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(r_lt)
            .map_err(|e| format!("Failed to assert Euclidean remainder upper bound: {e}"))?;

        self.euclid_div_mod_aliases.insert((dividend, d), (q, r));
        Ok((q, r))
    }

    /// Divisor-guarded Euclidean div/mod encoding for SYMBOLIC divisors
    /// (#2778 — nonlinear.rs `test4` and division-positivity shapes).
    ///
    /// ay leaves the native symbolic `(div a b)` / `(mod a b)` terms in its
    /// unsupported fragment and fail-closes the whole query to `Unknown`
    /// whenever one is present. So instead of the native terms, `a / b` and
    /// `a % b` are encoded as applications of two UNINTERPRETED functions
    /// `__euclid!div(a, b)` / `__euclid!mod(a, b)` (EUF — full functional
    /// congruence, unlike per-occurrence fresh constants), constrained by the
    /// divisor-guarded Euclidean lemma instances at each occurrence pair:
    ///
    /// 1. `b != 0 -> a == (a/b)*b + (a%b)`   (the defining reconstruction)
    /// 2. `b != 0 -> 0 <= a%b`               (non-negative remainder)
    /// 3. `b > 0  -> a%b < b`                (remainder bound, positive divisor)
    /// 4. `b < 0  -> a%b < -b`               (remainder bound, negative divisor;
    ///    3+4 together are exactly `b != 0 -> a%b < |b|` without needing `ite`)
    /// 5. `a >= 0 && b > 0 -> a/b >= 0`      (direct quotient-sign lemma; a
    ///    consequence of 1–3 whose derivation needs *nonlinear* reasoning —
    ///    `q <= -1 && b >= 1 ==> q*b <= -b` — so it is instantiated directly
    ///    to keep test4-shaped goals inside decidable EUF+LIA)
    ///
    /// SOUNDNESS (never a false `Verified`): interpret `__euclid!div` /
    /// `__euclid!mod` as the SMT-LIB Euclidean `div`/`mod`. Every asserted
    /// lemma is VALID under that interpretation — 1–4 are the SMT-LIB
    /// definition guarded by `b != 0`, and 5 is a theorem of it (`a >= 0, b >=
    /// 1 ==> floor(a/b) >= 0`). So any model of the original semantics extends
    /// to a model of this encoding, and `UNSAT` here implies `UNSAT` there:
    /// `Verified` is sound. Division by zero stays UNINTERPRETED — every lemma
    /// carries a divisor-sign/non-zero antecedent, so nothing constrains
    /// `a/0` / `a%0` (Verus spec `x/0`, `x%0` are likewise uninterpreted;
    /// never folded to a constant).
    ///
    /// COUNTEREXAMPLE FIDELITY: in a model of this encoding the UF values are
    /// forced to the true Euclidean values wherever the divisor is non-zero
    /// (lemmas 1–4 pin them uniquely), and at zero divisors any functionally
    /// consistent choice is a legitimate SMT-LIB div/mod-at-zero
    /// interpretation. So reported counterexamples correspond to genuine
    /// models of the original semantics — the UF (rather than fresh-constant)
    /// choice is what preserves the congruence SMT-LIB requires at zero.
    ///
    /// GATING: callers invoke this at `quantifier_depth == 0` only — the
    /// ground lemmas are asserted at the outer solver scope and must not
    /// reference enclosing bound variables (same discipline as
    /// `euclidean_literal_divisor` and the overflow side-checks, #2557).
    /// Inside quantifier bodies the native term is returned without lemmas:
    /// status quo, fail-closed `Unknown`. Lemma instances are deduped per
    /// `(dividend, divisor)` pair via `euclid_guarded_lemma_pairs`.
    fn guarded_euclidean_div_mod_symbolic(
        &mut self,
        dividend: Term,
        divisor: Term,
    ) -> TrustVcResult<(Term, Term)> {
        use ay_dpll::api::Sort;

        debug_assert_eq!(
            self.quantifier_depth, 0,
            "guarded Euclidean UF lemmas must only be asserted at the outer scope"
        );

        let (div_uf, mod_uf) = match self.euclid_ufs.clone() {
            Some(ufs) => ufs,
            None => {
                let div_uf = self
                    .solver
                    .try_declare_fun("__euclid!div", &[Sort::Int, Sort::Int], Sort::Int)
                    .map_err(|e| format!("Failed to declare __euclid!div: {e}"))?;
                let mod_uf = self
                    .solver
                    .try_declare_fun("__euclid!mod", &[Sort::Int, Sort::Int], Sort::Int)
                    .map_err(|e| format!("Failed to declare __euclid!mod: {e}"))?;
                self.euclid_ufs = Some((div_uf.clone(), mod_uf.clone()));
                (div_uf, mod_uf)
            }
        };

        let q = self
            .solver
            .try_apply(&div_uf, &[dividend, divisor])
            .map_err(|e| e.to_string())?;
        let r = self
            .solver
            .try_apply(&mod_uf, &[dividend, divisor])
            .map_err(|e| e.to_string())?;

        if !self.euclid_guarded_lemma_pairs.insert((dividend, divisor)) {
            return Ok((q, r));
        }

        let zero = self.solver.int_const(0);

        // guard: b != 0
        let d_eq_zero = self
            .solver
            .try_eq(divisor, zero)
            .map_err(|e| e.to_string())?;
        let guard = self.solver.try_not(d_eq_zero).map_err(|e| e.to_string())?;

        // (1) b != 0 -> a == q*b + r
        let qd = self.solver.try_mul(q, divisor).map_err(|e| e.to_string())?;
        let recon = self.solver.try_add(qd, r).map_err(|e| e.to_string())?;
        let recon_eq = self
            .solver
            .try_eq(recon, dividend)
            .map_err(|e| e.to_string())?;
        let recon_lemma = self
            .solver
            .try_implies(guard, recon_eq)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(recon_lemma)
            .map_err(|e| format!("Failed to assert guarded Euclidean reconstruction: {e}"))?;

        // (2) b != 0 -> 0 <= r
        let r_nonneg = self.solver.try_ge(r, zero).map_err(|e| e.to_string())?;
        let r_nonneg_lemma = self
            .solver
            .try_implies(guard, r_nonneg)
            .map_err(|e| e.to_string())?;
        self.solver.try_assert_term(r_nonneg_lemma).map_err(|e| {
            format!("Failed to assert guarded Euclidean remainder lower bound: {e}")
        })?;

        // (3) b > 0 -> r < b
        let d_pos = self
            .solver
            .try_gt(divisor, zero)
            .map_err(|e| e.to_string())?;
        let r_lt_d = self.solver.try_lt(r, divisor).map_err(|e| e.to_string())?;
        let pos_bound_lemma = self
            .solver
            .try_implies(d_pos, r_lt_d)
            .map_err(|e| e.to_string())?;
        self.solver.try_assert_term(pos_bound_lemma).map_err(|e| {
            format!("Failed to assert guarded Euclidean positive-divisor bound: {e}")
        })?;

        // (4) b < 0 -> r < -b
        let d_neg = self
            .solver
            .try_lt(divisor, zero)
            .map_err(|e| e.to_string())?;
        let neg_d = self
            .solver
            .try_sub(zero, divisor)
            .map_err(|e| e.to_string())?;
        let r_lt_neg_d = self.solver.try_lt(r, neg_d).map_err(|e| e.to_string())?;
        let neg_bound_lemma = self
            .solver
            .try_implies(d_neg, r_lt_neg_d)
            .map_err(|e| e.to_string())?;
        self.solver.try_assert_term(neg_bound_lemma).map_err(|e| {
            format!("Failed to assert guarded Euclidean negative-divisor bound: {e}")
        })?;

        // (5) a >= 0 && b > 0 -> q >= 0
        let a_nonneg = self
            .solver
            .try_ge(dividend, zero)
            .map_err(|e| e.to_string())?;
        let sign_ante = self
            .solver
            .try_and(a_nonneg, d_pos)
            .map_err(|e| e.to_string())?;
        let q_nonneg = self.solver.try_ge(q, zero).map_err(|e| e.to_string())?;
        let sign_lemma = self
            .solver
            .try_implies(sign_ante, q_nonneg)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(sign_lemma)
            .map_err(|e| format!("Failed to assert guarded Euclidean quotient-sign lemma: {e}"))?;

        Ok((q, r))
    }
}
