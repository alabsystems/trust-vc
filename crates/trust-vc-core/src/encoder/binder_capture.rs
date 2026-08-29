//! BINDER-CAPTURE backstop for the encode-then-close axiom shape.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # The defect class
//!
//! Every spec-fn defining axiom, every broadcast lemma and every trait-method
//! axiom is built ENCODE-THEN-CLOSE:
//!
//! ```text
//!   let body = encode(expr);              // bound vars are ORDINARY TOP-LEVEL terms
//!   let axiom = solver.try_forall(&var_terms, body);
//!   solver.try_assert_term(axiom);
//! ```
//!
//! During `encode` there is no live solver binder, so `real_quantifier_depth`
//! is 0 and `quantifier_scopes` is EMPTY — nothing the encoder can consult says
//! that a binder is coming. Any helper reached from that encode which mints a
//! fresh const and asserts its defining equation with a TOP-LEVEL
//! `try_assert_term` therefore has that equation left OUTSIDE the `forall`,
//! while the const it returned is placed INSIDE it. The axiom silently loses
//! its dependence on the bound variable:
//!
//! ```text
//!   (assert (= __c (g x)))                   ; x stays FREE here
//!   (assert (forall ((x S)) (= (f x) __c)))  ; ... but is BOUND here
//! ```
//!
//! i.e. "`f` is a CONSTANT function". Two measured CARDINAL instances:
//!
//! * `bind_datatype_match_result` (datatype-valued `match`) —
//!   `forall|c: Color, d: Color| next(c) == next(d)` VERIFIED on pristine.
//! * `purified_euclidean_div_mod_literal` (`/`, `%` on `int`/`nat`) — worse,
//!   because the ground replay of the same body pins the const to a second
//!   value and the whole context becomes INCONSISTENT: `half(2) == 5` VERIFIED.
//!
//! # Why a per-site gate cannot be the whole fix
//!
//! ENUMERATED, not guessed. A sweep of `crates/trust-vc-core/src/encoder` for
//! functions that both mint a fresh const (`fresh_var` / `try_declare_const`)
//! and reach a `try_assert_term` finds **47 such helpers on
//! `AstExpressionParser`** — every one reachable from a spec-fn body encode —
//! plus 9 more on `AYEncoder` itself. Of the 47:
//!
//! * **2 are gated** on `pending_universal_closure` and inline their result
//!   instead of hoisting: `bind_datatype_match_result` (`match_encode.rs`) and
//!   `purified_euclidean_div_mod_literal` (`arith/int_arith.rs`). Those two
//!   keep their defining axiom.
//! * **1 LOOKS gated and is not**: `reinterpret_bv_signedness`
//!   (`ir_encoder/cast.rs`) consults `is_quantifier_bound_term`, which reads
//!   the EMPTY `quantifier_scopes` and so never fires during an
//!   encode-then-close. It is the measured instance that reaches the backstop;
//!   see the known-open pin in `tests/hoist_capture_class.rs`.
//! * **9 assert a defining equation at the TOP LEVEL with no gate at all** —
//!   the highest-risk siblings: `collection_seq/ops.rs::encode_seq_occurrence_count`,
//!   `collection_seq_native/core_ops.rs::native_seq_last`,
//!   `collection_seq_native/helpers.rs::register_guarded_native_seq_len`,
//!   `collection_shared.rs::len_index_companion_inner`,
//!   `ir_encoder/cast.rs::guard_real_to_nat_cast_nonnegative`,
//!   `ir_encoder/collection_methods.rs::encode_push`,
//!   `ir_encoder/collection_set_map_inline.rs::native_string_len_term`,
//!   `ir_encoder/indexing.rs::encode_trust_vc_insert`,
//!   `ir_encoder/indexing.rs::encode_map_remove`.
//! * **34 wrap their hoist in a `try_forall`/`try_exists`.** That does NOT make
//!   them safe: the quantified assertion's own FREE terms (the source
//!   collection, its length) can still be terms the pending closure is about to
//!   bind.
//!
//! Gating 47 sites one at a time closes the instances someone thought to look
//! for and leaves the class open — and any helper added later inherits the
//! defect silently.
//!
//! # The backstop
//!
//! This module closes the class at the place it is defined: the closure
//! boundary. Take an assertion watermark before encoding; after encoding,
//! before building the `forall`, ask whether any assertion added in between
//! mentions a term that is about to be bound. If one does, the axiom would be
//! captured, so it is NOT emitted at all.
//!
//! The guard is WIRED PER BOUNDARY, and that is the module's honest limit: a
//! hoisting HELPER — enumerated above or added later — cannot escape a wired
//! boundary, but a NEW encode-then-close boundary is covered only once it
//! takes a watermark itself. The wired boundaries, enumerated not guessed
//! (every `try_forall*` closing over an encoded USER expression in this
//! crate):
//!
//! * `fuel.rs` — the spec-fn defining axioms;
//! * `trait_encoding_axioms.rs` — all four trait-axiom emitters;
//! * `verification/broadcast.rs` — the broadcast-lemma `forall`s;
//! * `datatype_invariants.rs` — the type-invariant defining axiom;
//! * `ir_encoder/choose.rs` — the `choose` Skolem-witness axiom.
//!
//! Adding an axiom emitter? If it encodes a body while its variables are
//! ordinary top-level terms and then closes with `try_forall*`, it MUST take
//! `assertion_watermark()` (`watermark(solver)` from a parser context) before
//! the encode, set `pending_universal_closure` for the encode's duration, and
//! check the capture scan before asserting.
//!
//! ## Soundness
//!
//! Declining to assert a defining axiom only WEAKENS the solver context
//! RELATIVE TO THE SAME ENCODE WITHOUT THE BACKSTOP — that relative statement
//! is the entire soundness argument, and it needs nothing else. The hoisted
//! assertions the body encode leaves behind are exactly the assertions the
//! ungated encoder emits on the same input; the backstop adds no assertion and
//! removes exactly one: the `forall` that would have captured them. The
//! function stays uninterpreted for symbolic reasoning (ground-pool replay,
//! which re-encodes per concrete instance and therefore cannot be captured, is
//! unaffected). No OBLIGATION is dropped; UNSAT gets harder, never easier. The
//! failure mode of the backstop is a lost proof, never a false `Verified`.
//!
//! MEASURED COST, not assumed: on the one site that actually reaches the
//! backstop in the test corpus (`sflip`, `x as i32`), declining the axiom cost
//! NOTHING — `t_cast_one_is_one`, `t_cast_symbolic` and `t_cast_nonneg` all
//! still verify through the ground-pool replay. The mutation arm confirms the
//! backstop is what closes that site: with `binder_capture_since` forced to
//! `None` and nothing else changed, `sflip(0) == sflip(1)` (FALSE) reports
//! `Verified` in 0.04 s.
//!
//! The hoisted assertions themselves are left in place. What the argument
//! above deliberately does NOT claim is that they are a conservative
//! extension. That is true of the two MEASURED sites (`__euclid_*` and the
//! cast consts are fresh, each constrained by a single defining equation) and
//! FALSE in general: `ir_encoder/indexing.rs::encode_map_remove` hoists
//! `new_len >= 0` and `new_len <= old_len` ungated at the top level, and
//! together those constrain the PRE-EXISTING `old_len` (they entail
//! `old_len >= 0`) — and `collection_shared.rs`'s guarded-companion comment
//! records that exactly this shape of unguarded length fact has poisoned a
//! context to UNSAT before. That exposure belongs to the nine ungated
//! hoisters themselves: it is present with or without this module, on every
//! encode path, and the backstop neither widens nor narrows it. The RELATIVE
//! argument above is therefore the one this module stands on.
//!
//! `HoistCapturedByPendingBinder` is NON-DEMOTING, and demotion was considered
//! and REJECTED rather than overlooked: an approximation demotes when it can
//! turn a refutation into a `Verified`, and removing an assertion cannot —
//! while demoting would withhold measured-correct proofs (the `t_cast_*` goals
//! in `tests/hoist_capture_class.rs`, which verify through ground replay after
//! `sflip`'s axiom is declined) for zero soundness gain.
//!
//! ## Cost, stated honestly
//!
//! ay exposes no O(1) assertion count: `Solver::assertions()` allocates a
//! `Vec<Term>` of the whole top-level stack, and this module calls it once at
//! the watermark (only for `.len()`) and once at the check; `term_children`
//! allocates a fresh `Vec` per visited node. The scan memoises capture-FREE
//! subtrees across the fresh assertions (`clean` below), so a shared sub-DAG
//! is walked once per closure site rather than once per assertion — but the
//! two full-stack allocations are O(|assertions|) per encode-then-close site,
//! i.e. quadratic in axiom count over a whole encode. Against solver time this
//! was not measurable on the corpus; on a timeout-marginal query it may be. An
//! ay-side assertion-count / assertions-since API is the fix if it ever is.
//!
//! ## Identity discipline
//!
//! Comparison is on `ay_dpll::api::Term` values, which carry arena and
//! entry-birth authority. No `TermId` is ever compared numerically and nothing
//! crosses a `TermStore` boundary: the watermark, the scan and the bound terms
//! all come from the same live `Solver`.

use std::collections::HashSet;

use ay_dpll::api::{Solver, Term};

use super::diagnostics::{EncodingApproximation, EncodingDiagnostics};
use super::AYEncoder;

/// A snapshot of the solver's top-level assertion stack.
///
/// Records the scope depth as well as the assertion count: a `push`/`pop` pair
/// during encoding could leave the count unchanged while replacing the tail, so
/// a scope change is treated as "cannot prove absence of capture".
#[derive(Debug, Clone, Copy)]
pub(in crate::encoder) struct AssertionWatermark {
    len: usize,
    scopes: u32,
}

/// Why an encode-then-close axiom was declined.
#[derive(Debug, Clone)]
pub(in crate::encoder) struct BinderCapture {
    /// How many freshly hoisted top-level assertions mention a to-be-bound term.
    pub(in crate::encoder) captured_assertions: usize,
    /// SMT-LIB rendering of those assertions, for diagnostics and for the
    /// enumeration of capture sites (the fresh-const name prefix identifies the
    /// minting helper).
    pub(in crate::encoder) rendered: String,
}

/// Snapshot the top-level assertion stack before an encode-then-close body is
/// encoded.
///
/// Free function so closure boundaries inside `AstExpressionParser` (which
/// holds `&mut Solver` and cannot reach `AYEncoder`) can take one too.
pub(in crate::encoder) fn watermark(solver: &Solver) -> AssertionWatermark {
    AssertionWatermark {
        len: solver.assertions().len(),
        scopes: solver.num_scopes(),
    }
}

/// Report whether closing a `forall` over `var_terms` would capture a fact
/// hoisted to the solver top level since `watermark`.
///
/// `None` means "provably not captured — emit the axiom". `Some(_)` means the
/// axiom must not be built; see the module docs.
pub(in crate::encoder) fn capture_since(
    solver: &Solver,
    watermark: AssertionWatermark,
    var_terms: &[Term],
) -> Option<BinderCapture> {
    if var_terms.is_empty() {
        // Nothing is bound, so nothing can be captured. (This is also the
        // `try_assert_term(body)` branch, which emits no binder at all.)
        return None;
    }

    let assertions = solver.assertions();
    if solver.num_scopes() != watermark.scopes || assertions.len() < watermark.len {
        // The assertion stack was re-shaped underneath us; we cannot prove
        // the tail is capture-free, so fail closed.
        return Some(BinderCapture {
            captured_assertions: 0,
            rendered: "<assertion stack reshaped during encode>".to_string(),
        });
    }
    let fresh = &assertions[watermark.len..];
    if fresh.is_empty() {
        return None;
    }

    let bound: HashSet<Term> = var_terms.iter().copied().collect();
    let mut offenders: Vec<Term> = Vec::new();
    // Terms proven capture-free. Whether a subtree contains a bound term is a
    // property of the TERM, not of the assertion it appears under, so a
    // subtree fully explored without finding one need never be walked again —
    // across assertions too. Merged only on capture-free COMPLETION: a walk
    // broken early proves nothing about the terms still on its stack.
    let mut clean: HashSet<Term> = HashSet::new();
    for &assertion in fresh {
        let mut visited: HashSet<Term> = HashSet::new();
        let mut stack = vec![assertion];
        let mut captured = false;
        while let Some(term) = stack.pop() {
            if clean.contains(&term) || !visited.insert(term) {
                continue;
            }
            if bound.contains(&term) {
                captured = true;
                break;
            }
            stack.extend(solver.term_children(term));
        }
        if captured {
            offenders.push(assertion);
        } else {
            clean.extend(visited);
        }
    }

    if offenders.is_empty() {
        return None;
    }
    Some(BinderCapture {
        rendered: solver.assertions_sexpr(&offenders),
        captured_assertions: offenders.len(),
    })
}

/// Record a declined encode-then-close axiom.
///
/// Emits the `TRUST_VC_BINDER_CAPTURE_TRACE` line when that env var is set —
/// that is how the sibling capture sites were ENUMERATED across the corpus
/// rather than guessed at by grep.
///
/// Free function for the same reason as [`watermark`]: parser-side closure
/// boundaries record into the parser's own `EncodingDiagnostics`, which is
/// merged into the encoder's afterwards.
pub(in crate::encoder) fn record_capture(
    diagnostics: &mut EncodingDiagnostics,
    site: &str,
    capture: &BinderCapture,
) {
    diagnostics.record(EncodingApproximation::HoistCapturedByPendingBinder);
    if std::env::var_os("TRUST_VC_BINDER_CAPTURE_TRACE").is_some() {
        let flat = capture.rendered.replace('\n', " ");
        eprintln!(
            "TRUST_VC_BINDER_CAPTURE\tsite={site}\tcount={}\t{flat}",
            capture.captured_assertions
        );
    }
}

impl AYEncoder {
    /// [`watermark`], from encoder context.
    pub(in crate::encoder) fn assertion_watermark(&self) -> AssertionWatermark {
        watermark(&self.solver)
    }

    /// [`capture_since`], from encoder context.
    pub(in crate::encoder) fn binder_capture_since(
        &self,
        watermark: AssertionWatermark,
        var_terms: &[Term],
    ) -> Option<BinderCapture> {
        capture_since(&self.solver, watermark, var_terms)
    }

    /// [`record_capture`], into the encoder's own diagnostics.
    pub(in crate::encoder) fn record_binder_capture(&mut self, site: &str, capture: &BinderCapture) {
        record_capture(&mut self.state.diagnostics, site, capture)
    }
}
