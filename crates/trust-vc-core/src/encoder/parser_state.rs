//! AST parser state — types, constructor, and lifecycle helpers.
//!
//! Collection metadata helpers live in `collection_state.rs`.
//! Width inference and BV coercion helpers live in `width_coercion.rs`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::borrow::Cow;

use ay_dpll::api::{FuncDecl, Solver, Term};

/// A labeled overflow check: `(label, guard_term)`.
pub(in super::super) type OverflowCheck = (Cow<'static, str>, Term);

/// A constant-folded overflow verdict: `(label, overflows)`.
///
/// `overflows == true` means the all-constant operation definitely overflows
/// its result type (a counterexample); `false` means it is definitely safe.
/// See `AstExpressionParser::const_fold_overflow_verdicts`.
pub(in super::super) type ConstFoldOverflowCheck = (Cow<'static, str>, bool);

use super::arith_semantics::ArithSemantics;
use super::ground_pool::GroundTermPool;
use super::quantifier_scope::QuantifierScope;

/// Discriminant for spec-collection type family.
///
/// Used in term-keyed metadata (`CollectionMeta`) so that dispatch logic
/// (e.g., `contains` routing, bounds checks) can resolve semantics from an
/// anonymous result term without needing a variable name.  Mirrors the
/// `TrustVcType::Seq | Set | Multiset | Map` variants but carries no generic payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum CollectionKind {
    Seq,
    Set,
    Multiset,
    Map,
}

/// Projection-view kind for Seq-derived Set/Multiset carrier terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum DerivedSeqViewKind {
    SetView,
    MultisetView,
}

/// Provenance for an opaque Set/Multiset carrier derived from a source Seq.
#[derive(Debug, Clone)]
pub(super) struct DerivedSeqView {
    pub(super) kind: DerivedSeqViewKind,
    pub(super) source_term: Term,
    pub(super) source_name: Option<String>,
}

/// Declaration-time native Seq mirror keyed by the encoder-facing source term.
#[cfg(feature = "native-seq")]
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub(super) struct NativeSeqShadow {
    pub(super) native_term: Term,
    pub(super) len_int_term: Term,
    pub(super) source_term: Term,
    pub(super) source_name: Option<String>,
    pub(super) elem_ty: crate::ir::TrustVcType,
}

/// Cached `String/str -> Seq<char>` view shadow keyed by the source string term.
#[cfg(feature = "native-strings")]
#[derive(Debug, Clone)]
pub(super) struct NativeStringViewShadow {
    pub(super) view_term: Term,
    pub(super) len_term: Term,
}

#[cfg(feature = "native-seq")]
pub(super) fn native_seq_shadow_var_name(source_name: &str) -> String {
    format!("__trust_vc_native_seq_shadow_{source_name}")
}

/// Per-term metadata for a collection value (named variable OR anonymous result).
///
/// Follows the same pattern as `term_widths: HashMap<Term, (u32, bool)>` —
/// term-keyed metadata that survives across method-call boundaries.
#[derive(Debug, Clone)]
pub(super) struct CollectionMeta {
    pub(super) kind: CollectionKind,
    /// Length / cardinality term (BitVec(pointer_width()), unsigned).
    /// `None` only for intermediate terms whose length is not yet computed.
    pub(super) len_term: Option<Term>,
    /// Optional soundness guard that must hold before the length term is used.
    /// Derived collection results attach path-sensitive no-wrap conditions here
    /// so non-length operations do not pay unrelated verification cost.
    pub(super) len_guard: Option<(Cow<'static, str>, Term)>,
    /// Element type for sort resolution without name fallback (#2067).
    /// Seq<T>/Set<T>/Multiset<T> → T, Map<K,V> → V.
    /// `None` when element type is not determinable at construction.
    pub(super) elem_ty: Option<crate::ir::TrustVcType>,
    /// Key type for Map types (#2507). Enables `map_key_value_types` to resolve
    /// key type from term-keyed metadata for anonymous chained receivers.
    /// `None` for Seq/Set/Multiset or when key type is not determinable.
    pub(super) key_ty: Option<crate::ir::TrustVcType>,
    /// Domain membership array for Map types: Array(K, Bool).
    /// Tracks which keys have been explicitly inserted. `None` for Seq/Set/Multiset.
    /// Created by `declare_variable` for Map variables (#1966).
    /// Read by `lookup_collection_dom` (term-keyed path) with `domain_terms`
    /// HashMap fallback for name-keyed callers.
    pub(super) dom_term: Option<Term>,
}

/// Same-index read-back provenance for a `Seq::push` result term.
///
/// A `db.push(v)` result is `store(db, int2bv(old_len), v)`; the immediately
/// following `db.index(db.len() - 1)` reduces (push-length axiom
/// `new_len == old_len + 1`, then ay's linear fold) to a select at the SAME
/// `old_len`. Because store and select alias the identical (possibly wrapped)
/// carrier cell, ay's read-over-write yields `v` EXACTLY — independent of
/// whether `int2bv(old_len)` is carrier-representable. This record lets
/// `encode_seq_get`/`encode_index` recognize that shape and reuse the store's
/// own index term, so no spurious representability obligation is minted for the
/// select and the store-side one can be retracted. STRICTLY scoped: the
/// recognizer fires only when the select carrier index is structurally
/// IDENTICAL to `store_index` (never "index looks like len - c", never "a push
/// happened recently").
#[derive(Debug, Clone, Copy)]
pub(super) struct PushReadback {
    /// The BitVec(pointer_width) carrier index written by the push
    /// (`append_idx_bv` = `int2bv(pw, old_len)` in the symbolic-length case).
    pub(super) store_index: Term,
    /// The Int `old_len` that `store_index` is `int2bv` of, when the store index
    /// crossed via a wrapping `int2bv` (the only case that queued a carrier
    /// representability obligation). `None` for a finite/literal push whose
    /// index is a representable BV constant (nothing to retract).
    pub(super) store_index_int: Option<Term>,
}

/// AST-based expression parser — the sole expression parser.
/// Parses `syn::Expr` AST nodes into ay SMT terms.
#[doc(hidden)]
pub struct AstExpressionParser<'a> {
    pub(super) solver: &'a mut Solver,
    pub(super) variables: &'a std::collections::HashMap<String, Term>,
    pub(super) collection_lengths: &'a mut std::collections::HashMap<String, Term>,
    pub(super) var_types: &'a std::collections::HashMap<String, crate::ir::TrustVcType>,
    /// Declared uninterpreted functions for recursive function call encoding.
    pub(super) functions: &'a std::collections::HashMap<String, FuncDecl>,
    /// Registered function return types, including zero-arity helpers that are
    /// encoded as constants instead of `FuncDecl`s.
    ///
    /// This stays optional so direct parser tests can keep using the minimal
    /// constructor without threading another reference through every call site.
    pub(super) function_return_types:
        Option<&'a std::collections::HashMap<String, crate::ir::TrustVcType>>,
    /// Track BitVec widths and signedness of created terms for width coercion.
    /// Maps terms to (width, is_signed). Non-BitVec terms are not tracked.
    pub(super) term_widths: std::collections::HashMap<Term, (u32, bool)>,
    /// Locally-bound variables from quantifier scopes (forall/exists).
    /// These shadow the outer `variables` map while parsing quantifier bodies.
    pub(super) local_vars: std::collections::HashMap<String, Term>,
    /// Types of locally-bound variables for signedness/width inference.
    pub(super) local_var_types: std::collections::HashMap<String, crate::ir::TrustVcType>,
    /// Nesting depth of quantifier bodies being parsed.
    /// When > 0, integer operations use `Sort::Int` (arithmetic) instead of bitvectors.
    pub(super) quantifier_depth: usize,
    /// Portion of `quantifier_depth` whose bodies intentionally stay in BV
    /// arithmetic because all bound variables are finite-width BV terms.
    /// This separates "inside a quantifier" from "must use Int arithmetic".
    /// Part of #2862.
    pub(super) bv_quantifier_depth: usize,
    /// Nesting depth of genuinely *symbolic* quantifier binders currently in
    /// scope — positive `forall`/`exists` whose bound variable ranges over its
    /// whole (possibly infinite) domain. Deliberately EXCLUDES the ground Skolem
    /// witnesses introduced by `encode_forall_refutation` (an assertion's negated
    /// `forall`), which are fixed constants.
    ///
    /// Multiset count reasoning keys off this to stay sound AND refutation-
    /// friendly: at depth 0 (ground / refutation-witness context) `count` is
    /// computed compositionally as a quantifier-free arithmetic term and the
    /// per-leaf `count >= 0` Nat invariant is asserted as a ground fact, so a
    /// false `=~=` refutation has NO MBQI-unsafe pointwise `forall` blocking ay
    /// from exhibiting a concrete differing-count witness. At depth > 0 (a real
    /// universal) the pointwise `forall` axioms are emitted instead, since a
    /// ground per-leaf assertion about a symbolic binder would be unsound.
    /// Part of #2779 (Multiset extensional-equality refutation witness).
    pub(super) symbolic_quantifier_depth: usize,
    /// Nesting depth of *real* (non-Skolemized) solver quantifiers currently in
    /// scope — i.e. every `exists` and every `forall` actually emitted as an
    /// `ay` quantifier (with or without triggers, in assumption context, or
    /// because it is itself nested under another real quantifier). EXCLUDES
    /// trigger-less assertion-position `forall`s that are Skolemized to a ground
    /// guarded body (their bound vars become free top-level vars).
    ///
    /// Soundness (P1-D, exists-forall quantifier-order swap): Skolemizing a
    /// trigger-less `forall` to free vars is sound ONLY when those free vars are
    /// universally closed at the *outermost* scope by verification-by-refutation.
    /// The moment the `forall` sits inside the scope of a real quantifier (e.g.
    /// `exists j. forall i. P`), Skolemizing it lets `i` leak OUTSIDE the
    /// `exists` and be closed at the top — silently swapping the strong `∃j.∀i`
    /// into the weak `∀i.∃j`. So when `real_quantifier_depth > 0`, a nested
    /// `forall` must stay a real `try_forall` quantifier instead of Skolemizing.
    pub(super) real_quantifier_depth: usize,
    /// True while the root expression for the current encode call has already
    /// passed iterative depth validation. Recursive re-entry must skip the
    /// validator to avoid re-scanning every subtree.
    pub(super) expr_depth_guard_active: bool,
    /// When true, forces Int arithmetic mode (same as quantifier_depth > 0).
    /// Set when all variables in the context use Sort::Int (no BV variables).
    /// Used for termination proofs where mathematical integers are appropriate (#1605).
    pub(super) use_int_arithmetic: bool,
    /// Active obligation solver mode, threaded from `PreparedObligation`.
    /// BitVector mode preserves concrete finite-width quantifiers instead of
    /// widening their bound variables to Int. Part of #2862.
    pub(super) solver_mode: Option<crate::vc::SolverMode>,
    /// Explicit scoped metadata for quantifier-bound variables (#2046).
    /// The IR encoder resolves arithmetic semantics from this scope stack
    /// via `current_quantifier_wrap_semantics()`.
    pub(super) quantifier_scopes: Vec<QuantifierScope>,
    /// Whether to generate overflow checking predicates for arithmetic operations.
    /// When `should_check()` is true, arithmetic ops (+, -, *) generate additional
    /// boolean terms that assert the operation does not overflow/underflow the
    /// bitvector bounds. Part of #2516.
    pub(super) overflow_behavior: crate::vc::OverflowBehavior,
    /// Whether to generate division-by-zero checking predicates.
    /// When `should_check()` is true, division and remainder ops generate a
    /// non-zero divisor predicate. Part of #2516.
    pub(super) div0_behavior: crate::vc::Div0Behavior,
    /// Whether to generate shift amount bounds checking predicates.
    /// When `should_check()` is true, shift ops generate a predicate asserting
    /// the shift amount is less than the bit width. Part of #2516.
    pub(super) bitshift_behavior: crate::vc::BitshiftBehavior,
    /// Collected overflow checking predicates. Each entry is a (name, predicate) pair
    /// where the predicate is a boolean term that is TRUE when no overflow occurs.
    /// The caller must assert these as additional proof obligations.
    pub(super) overflow_checks: Vec<OverflowCheck>,
    /// Constant-folded definite overflow verdicts (#2778).
    ///
    /// When an arithmetic operation has all-constant operands of a known finite
    /// width, the encoder evaluates the overflow obligation exactly here instead
    /// of emitting a symbolic `bvadd_no_overflow`-style predicate (which returns
    /// SAT with an empty model for fully-ground queries — an ay-dpll CEGQI
    /// artifact, not a real verdict). Each entry is a `(label, overflows)` pair;
    /// `overflows == true` is a definite counterexample, `false` is definitely
    /// safe. Consumed by `check_overflow_predicates`.
    pub(super) const_fold_overflow_verdicts: Vec<ConstFoldOverflowCheck>,
    /// When true, the encoder is encoding an assumption (not an assertion).
    /// Trigger-less forall in assumptions must NOT be Skolemized — they need
    /// a real `solver.forall()` quantifier to preserve universal strength.
    /// Skolemization is only correct for assertions (negated by refutation).
    pub(super) in_assumption_context: bool,
    /// When true, a TOP-LEVEL positive assumption existential is eager-Skolemized
    /// to fresh consts at ENCODE time (pre-watermark) rather than emitted as a
    /// real `try_exists` (whose Skolem witness is minted during solving,
    /// post-watermark, and thus blocked from E-matching a `no_mbqi` axiom).
    /// Consumed in `encode_quantifier`'s `Exists` arm, gated on
    /// `real_quantifier_depth == 0` so it fires ONLY for the outermost (genuinely
    /// positive, top-level) existential and never a nested one. Set exclusively
    /// by `add_typed_assumption_inner` for a literal top-level `Exists`
    /// assumption; never on the goal/refutation path. See the field on
    /// `EncoderState` for the full soundness argument.
    pub(super) skolemize_top_level_assumption_exists: bool,
    /// When true, quantified assumptions keep bound variables at their
    /// concrete backend sorts instead of widening integer-like types to Int.
    /// Used for reintroduced `assert_forall_by` facts whose bodies mention
    /// helper UFs declared over concrete integer sorts. Part of #2551.
    pub(super) preserve_assumption_quantifier_sorts: bool,
    /// Term-keyed collection metadata (#1749).
    ///
    /// Canonical source of kind + length for collection values, including
    /// anonymous results from chained method calls (e.g., `s.push(v).len()`).
    /// `collection_lengths` remains for backward compatibility during migration;
    /// new code should prefer `lookup_collection_len()` which resolves here first.
    pub(super) collection_meta_by_term: std::collections::HashMap<Term, CollectionMeta>,
    /// Same-index read-back provenance for `Seq::push` result terms (see
    /// [`PushReadback`]). Keyed by the push result (`store(..)`) term.
    pub(super) push_readback_by_term: std::collections::HashMap<Term, PushReadback>,
    /// Canonical aliases for repeated concrete native-seq element accesses.
    ///
    /// Keyed by `(receiver_term, concrete_index)` so repeated `seq.nth(s, 1)`
    /// reads inside one query reuse the same named term instead of relying on
    /// ay-dpll to merge duplicate ground sequence applications itself.
    #[cfg(feature = "native-seq")]
    pub(super) native_seq_ground_element_aliases: std::collections::HashMap<(Term, i128), Term>,
    /// Encoding diagnostics — tracks approximations for result demotion.
    /// Merged into AYEncoder.diagnostics after encoding completes. Part of #2224.
    pub(super) diagnostics: super::diagnostics::EncodingDiagnostics,
    /// Provenance for Multiset::union anonymous result terms.
    /// Maps union-result term -> (lhs, rhs) so downstream count/contains/update
    /// operations can inherit source well-formedness when they access the result.
    pub(super) multiset_union_sources: std::collections::HashMap<Term, (Term, Term)>,
    /// Provenance for Multiset::difference/sub anonymous result terms.
    /// Maps difference-result term -> (minuend, subtrahend, subtrahend_name) so
    /// downstream union/add can use saturating-subtraction facts.
    pub(super) multiset_difference_sources:
        std::collections::HashMap<Term, (Term, Term, Option<String>)>,
    /// Provenance for Multiset::intersect anonymous result terms.
    /// Maps intersect-result term -> (lhs, rhs) so `count` can be computed
    /// compositionally as the pointwise minimum without the array-indexing
    /// pointwise `forall`. Part of #2779.
    pub(super) multiset_intersect_sources: std::collections::HashMap<Term, (Term, Term)>,
    /// Provenance for anonymous Multiset results that must inherit well-formedness
    /// checks from their source operands.
    pub(super) multiset_operand_sources: std::collections::HashMap<Term, Vec<Term>>,
    /// Provenance for opaque Set/Multiset carriers derived from a source Seq.
    pub(super) derived_seq_views: std::collections::HashMap<Term, DerivedSeqView>,
    /// Native Seq mirrors keyed by the source carrier term.
    #[cfg(feature = "native-seq")]
    pub(super) native_seq_shadows: std::collections::HashMap<Term, NativeSeqShadow>,
    /// Cached Seq<char> shadows for native String / str view() receivers.
    #[cfg(feature = "native-strings")]
    pub(super) native_string_view_shadows: std::collections::HashMap<Term, NativeStringViewShadow>,
    /// Mutable domain terms for Map types (#1966). Updated by insert/remove.
    /// ContainsKey/Dom check here first, then fall back to `variables` for
    /// initial domain from `declare_variable`. Name-keyed: `{name}_dom`.
    pub(super) domain_terms: std::collections::HashMap<String, Term>,
    /// Optional encoder-owned ground-term pool for bounded fixpoint flushing.
    pub(super) ground_pool: Option<&'a mut GroundTermPool>,
    /// Per-function parameter types for polymorphic type binding inference.
    /// Part of #2053.
    pub(super) function_param_types:
        Option<&'a std::collections::HashMap<String, Vec<crate::ir::TrustVcType>>>,
    /// Per-function type parameter names for polymorphism. Part of #2053.
    pub(super) function_type_params: Option<&'a std::collections::HashMap<String, Vec<String>>>,
    /// Poly/Box/Unbox context for type-erased polymorphism encoding.
    /// Part of #2053.
    pub(super) poly_context: Option<&'a mut super::polymorphism::PolyContext>,
    /// Registry of Skolem functions for choose expressions. Same key →
    /// same function. Persists across encode calls within one verification
    /// query. Part of #2143.
    pub(super) choose_registry: Option<&'a mut std::collections::HashMap<String, FuncDecl>>,
    /// Well-foundedness size functions for recursive datatypes.
    /// Part of #2421 residual `__trust_vc_dt_size` lowering.
    pub(super) dt_size_funcs: Option<&'a std::collections::HashMap<String, FuncDecl>>,
    /// Registry of prophecy variables (fresh unconstrained constants) keyed by
    /// prophecy name. Part of #2519.
    pub(super) prophecy_registry: Option<&'a mut std::collections::HashMap<String, Term>>,
    /// Memoizes fail-closed nat-cast lowerings within one verification query.
    ///
    /// Keyed by `(source_term, NatCastKind)` → the lowered nat term (an `ite`
    /// over a floor/value and a fresh `__trust_vc_invalid_nat_cast` skolem).
    /// Re-encoding the *same* `expr as nat` reuses the cached term instead of
    /// minting a fresh floor/invalid skolem each time, so a ground
    /// `nat_to_real(expr as nat)` in an assertion and the matching ground-axiom
    /// instance share the identical argument term and connect via E-matching.
    /// Persisted across parser instances through `VerificationState`.
    pub(super) nat_cast_aliases:
        std::collections::HashMap<(Term, super::ir_encoder::cast::NatCastKind), Term>,
    /// Memoizes the native `(map.dom m)` domain projection for each Map value
    /// carrier `m`, bridged once to `m`'s tracked domain array by equality.
    ///
    /// trust-vc tracks a per-Map domain array (`{name}_dom`, updated by
    /// insert/remove). The native map theory (`ay-theories/map`) instead reasons
    /// about subset↔key obligations over the canonical `(map.dom m)` projection.
    /// To let `map.subset` decide membership/value propagation natively (no
    /// MBQI), `contains_key` reads through `(map.dom m)` and we assert
    /// `(map.dom m) == tracked_dom` once. The bridge is sound and verdict-neutral
    /// (it is literally the same array); it only changes the *syntactic* shape so
    /// ay's ground subset-witness discovery matches. Keyed by the value carrier
    /// term `m`. Owned (not borrowed): lives for one verification query.
    pub(super) map_dom_bridges: std::collections::HashMap<Term, Term>,
    /// Set once any `map.subset` atom is emitted in this query.
    ///
    /// Gates whether `contains_key` reads membership through the native
    /// `(map.dom m)` projection (so ay's finite-map theory can discover ground
    /// subset↔key witnesses and decide `map.subset` without MBQI) or through the
    /// plain tracked domain array (the array/BV path, which keeps non-subset Map
    /// queries — insert/contains_key/eq with BV-sorted length overflow checks —
    /// on QF_ABV/QF_AUFBV instead of forcing them onto QF_MAPLIA). Without this
    /// gate, every Map query would carry a `map.*` symbol and route to QF_MAPLIA,
    /// where BV-length overflow obligations cannot be decided (regression).
    /// Defaults false; flipping it is monotone within one query.
    pub(super) map_subset_seen: bool,
    /// Memoizes pure, deterministic spec-collection constructors
    /// (`Set::new`/`Set::map`/`Set::filter`) within one verification query.
    ///
    /// Keyed by a canonical structural key of the constructor (closure AST plus,
    /// for image ops, the source-set term id). The fresh-array-per-occurrence
    /// encoding gives two syntactically-identical comprehensions distinct backend
    /// arrays that merely share the SAME membership axiom; they are then
    /// extensionally equal but not term-identical, so E-matching cannot connect a
    /// mapped set's forward/reverse image axiom to a membership fact stated on a
    /// *different* occurrence of the same source set (e.g. `pos2.contains(i)` and
    /// `nonneg.contains(i-1)` for `pos2 = nonneg.map(|i| i+1)`). Sharing one term
    /// per closed constructor restores that identity. Sound: a constructor with no
    /// transient free variable denotes the same value at every occurrence, so this
    /// only adds a true equality the membership-only encoding omitted — it can
    /// never make a false goal provable. Bypassed (fresh encoding) when the
    /// constructor references a transient binding (`local_vars`), since the same
    /// syntax under different bindings may denote different values. Persisted
    /// across `AstExpressionParser` instances through `VerificationState`.
    pub(super) pure_collection_cache: std::collections::HashMap<String, Term>,
    /// Memoizes the purified Euclidean quotient/remainder pair for a div/mod by
    /// a LITERAL constant divisor within one encoded expression (#2778).
    ///
    /// Keyed by `(dividend_term, divisor_literal)` → `(quotient, remainder)`.
    /// Verus `int`/`nat` `a / d` and `a % d` (constant `d`) are purified to fresh
    /// `q`/`r` constrained by the Euclidean axioms `a == q*d + r ∧ 0 <= r < |d|`
    /// (`int_arith::purified_euclidean_div_mod_literal`). Encoding `a / d` and
    /// `a % d` as *separate* fresh pairs would force the solver to re-derive that
    /// the remainder is unique — a LIA-valid fact ay nonetheless returns `Unknown`
    /// on — so both spellings must resolve to the SAME `(q, r)`. This cache makes
    /// `(a/d)*d + a%d` collapse to `q*d + r`, which is trivially the asserted
    /// definition. SOUND: it only adds the true congruence "equal operands give
    /// equal div/mod results", never a new value. Owned per parser instance —
    /// both halves of one obligation's expression share an instance.
    pub(super) euclid_div_mod_aliases: std::collections::HashMap<(Term, i128), (Term, Term)>,
    /// Memoizes which `(dividend_term, divisor_term)` pairs already had the
    /// divisor-guarded Euclidean div/mod lemma instances asserted (#2778,
    /// SYMBOLIC divisors — the literal-divisor purification above handles
    /// constants).
    ///
    /// For each `a / b` / `a % b` over `int`/`nat` with a *symbolic* divisor
    /// (at `quantifier_depth == 0`),
    /// `int_arith::guarded_euclidean_div_mod_symbolic` encodes the result as
    /// an application of the uninterpreted functions `__euclid!div` /
    /// `__euclid!mod` and asserts the divisor-guarded SMT-LIB Euclidean facts
    /// about that application: `b != 0 -> a == (a/b)*b + a%b ∧ 0 <= a%b <
    /// |b|`, plus the direct quotient-sign lemma `a >= 0 ∧ b > 0 -> a/b >=
    /// 0`. Every asserted formula is VALID for the intended interpretation
    /// (Euclidean div/mod, which the guard leaves completely unconstrained at
    /// `b == 0` — exactly SMT-LIB's uninterpreted-at-zero semantics), so this
    /// is pure lemma instantiation: it can never make an invalid goal verify.
    /// This set only dedups re-assertion for repeated occurrences of the same
    /// pair. Owned per parser instance, like `euclid_div_mod_aliases`; the UF
    /// symbols themselves are global to the solver, so congruence holds
    /// across parser instances.
    pub(super) euclid_guarded_lemma_pairs: std::collections::HashSet<(Term, Term)>,
    /// Lazily-declared `(__euclid!div, __euclid!mod)` uninterpreted-function
    /// decls for the symbolic-divisor encoding above. The names contain `!`,
    /// which no Rust-derived user symbol can contain, so they can never
    /// collide with (and thus never conflate with) user functions.
    /// Redeclaration across parser instances is idempotent in ay.
    pub(super) euclid_ufs: Option<(FuncDecl, FuncDecl)>,
}

impl<'a> AstExpressionParser<'a> {
    pub fn new(
        solver: &'a mut Solver,
        variables: &'a std::collections::HashMap<String, Term>,
        collection_lengths: &'a mut std::collections::HashMap<String, Term>,
        var_types: &'a std::collections::HashMap<String, crate::ir::TrustVcType>,
        functions: &'a std::collections::HashMap<String, FuncDecl>,
    ) -> Self {
        Self::with_overflow_checking(
            solver,
            variables,
            collection_lengths,
            var_types,
            functions,
            false,
        )
    }

    pub fn with_overflow_checking(
        solver: &'a mut Solver,
        variables: &'a std::collections::HashMap<String, Term>,
        collection_lengths: &'a mut std::collections::HashMap<String, Term>,
        var_types: &'a std::collections::HashMap<String, crate::ir::TrustVcType>,
        functions: &'a std::collections::HashMap<String, FuncDecl>,
        check_overflow: bool,
    ) -> Self {
        let overflow_behavior = if check_overflow {
            crate::vc::OverflowBehavior::Error
        } else {
            crate::vc::OverflowBehavior::default_no_check()
        };
        Self::with_overflow_behavior(
            solver,
            variables,
            collection_lengths,
            var_types,
            functions,
            overflow_behavior,
        )
    }

    /// Constructor with explicit overflow behavior. Part of #2516.
    pub fn with_overflow_behavior(
        solver: &'a mut Solver,
        variables: &'a std::collections::HashMap<String, Term>,
        collection_lengths: &'a mut std::collections::HashMap<String, Term>,
        var_types: &'a std::collections::HashMap<String, crate::ir::TrustVcType>,
        functions: &'a std::collections::HashMap<String, FuncDecl>,
        overflow_behavior: crate::vc::OverflowBehavior,
    ) -> Self {
        // Pre-populate term_widths from known variables
        let mut term_widths = std::collections::HashMap::new();
        for (name, term) in variables {
            if let Some(ty) = var_types.get(name) {
                if let Some(w) = ty.bit_width() {
                    if w > 0 {
                        let signed = !ty.is_unsigned();
                        term_widths.insert(*term, (w, signed));
                    }
                }
            }
        }
        // Collection lengths are pointer_width, unsigned (#1745).
        // Matches Seq index sort and Rust's usize semantics.
        // Under native-seq, Seq lengths are Int-sorted (from seq.len),
        // not BV. Only register BV-sorted length terms. #2680.
        let pw = crate::ir::pointer_width();
        for term in collection_lengths.values() {
            if matches!(solver.term_sort(*term), ay_dpll::api::Sort::Int) {
                continue;
            }
            term_widths.insert(*term, (pw, false));
        }

        // Pre-populate domain_terms from declared Map variables (#1966).
        // declare_variable stores {name}_dom in variables for Map types.
        let mut domain_terms = std::collections::HashMap::new();
        for (name, ty) in var_types.iter() {
            if matches!(ty, crate::ir::TrustVcType::Map(_, _)) {
                let dom_name = format!("{}_dom", name);
                if let Some(&dom) = variables.get(&dom_name) {
                    domain_terms.insert(dom_name, dom);
                }
            }
        }

        // Pre-populate term-keyed collection metadata from declared variables (#1749).
        let mut collection_meta_by_term = std::collections::HashMap::new();
        for (name, term) in variables.iter() {
            if let Some(ty) = var_types.get(name) {
                let kind = match ty {
                    crate::ir::TrustVcType::Seq(_) | crate::ir::TrustVcType::Array(_, _) => {
                        Some(CollectionKind::Seq)
                    }
                    crate::ir::TrustVcType::Set(_) => Some(CollectionKind::Set),
                    crate::ir::TrustVcType::Multiset(_) => Some(CollectionKind::Multiset),
                    crate::ir::TrustVcType::Map(_, _) => Some(CollectionKind::Map),
                    _ => None,
                };
                if let Some(kind) = kind {
                    let len_term = collection_lengths.get(name).copied();
                    let elem_ty = ty.collection_elem();
                    let dom_term = domain_terms.get(&format!("{}_dom", name)).copied();
                    let key_ty = match ty {
                        crate::ir::TrustVcType::Map(k, _) => Some(k.as_ref().clone()),
                        _ => None,
                    };
                    collection_meta_by_term.insert(
                        *term,
                        CollectionMeta {
                            kind,
                            len_term,
                            len_guard: None,
                            elem_ty,
                            key_ty,
                            dom_term,
                        },
                    );
                }
            }
        }

        // Use Int arithmetic only when the session has no BV-backed variables,
        // at least one scalar MathInt/Nat/Real variable that actually needs the
        // mode, and no floating-point variables. This keeps MathInt+Datatype /
        // MathInt+Bool sessions on the LIA path without re-enabling float-only
        // contexts or Seq/Datatype-only sessions that do not need scalar Int mode.
        let has_int_mode_seed = var_types.values().any(|ty| {
            matches!(
                ty,
                crate::ir::TrustVcType::MathInt
                    | crate::ir::TrustVcType::Nat
                    | crate::ir::TrustVcType::Real
            )
        });
        let has_float = var_types
            .values()
            .any(crate::ir::TrustVcType::contains_float);
        let use_int_arithmetic =
            term_widths.is_empty() && !variables.is_empty() && has_int_mode_seed && !has_float;
        #[cfg(feature = "native-seq")]
        let mut native_seq_shadows = std::collections::HashMap::new();
        #[cfg(feature = "native-seq")]
        for (name, term) in variables.iter() {
            let elem_ty = match var_types.get(name) {
                Some(crate::ir::TrustVcType::Seq(elem_ty))
                | Some(crate::ir::TrustVcType::Array(elem_ty, _)) => elem_ty,
                _ => continue,
            };
            let shadow_name = native_seq_shadow_var_name(name);
            let Some(&native_term) = variables.get(&shadow_name) else {
                continue;
            };
            // Native seq shadow metadata must remain Seq-sorted for the soundness bridge.
            let len_int_term = solver
                .try_seq_len(native_term)
                .expect("invariant: native shadow declarations must stay Seq-sorted"); // quality-audit: allow-expect
            native_seq_shadows.insert(
                *term,
                NativeSeqShadow {
                    native_term,
                    len_int_term,
                    source_term: *term,
                    source_name: Some(name.clone()),
                    elem_ty: elem_ty.as_ref().clone(),
                },
            );
        }
        // Derive div0 from overflow_behavior for backward compatibility.
        // Error → check, Allow/Truncate → don't check.
        let div0_behavior = if overflow_behavior.should_check() {
            crate::vc::Div0Behavior::Error
        } else {
            crate::vc::Div0Behavior::Allow
        };
        // Bitshift UB is always checked in BV mode (default = Error).
        // In int-mode, shift UB doesn't apply (no bitvector semantics).
        let bitshift_behavior = crate::vc::BitshiftBehavior::default();
        Self {
            solver,
            variables,
            collection_lengths,
            var_types,
            functions,
            function_return_types: None,
            term_widths,
            local_vars: std::collections::HashMap::new(),
            local_var_types: std::collections::HashMap::new(),
            quantifier_depth: 0,
            bv_quantifier_depth: 0,
            symbolic_quantifier_depth: 0,
            real_quantifier_depth: 0,
            expr_depth_guard_active: false,
            use_int_arithmetic,
            solver_mode: None,
            quantifier_scopes: Vec::new(),
            overflow_behavior,
            div0_behavior,
            bitshift_behavior,
            overflow_checks: Vec::new(),
            const_fold_overflow_verdicts: Vec::new(),
            in_assumption_context: false,
            skolemize_top_level_assumption_exists: false,
            preserve_assumption_quantifier_sorts: false,
            collection_meta_by_term,
            push_readback_by_term: std::collections::HashMap::new(),
            #[cfg(feature = "native-seq")]
            native_seq_ground_element_aliases: std::collections::HashMap::new(),
            diagnostics: super::diagnostics::EncodingDiagnostics::default(),
            multiset_union_sources: std::collections::HashMap::new(),
            multiset_difference_sources: std::collections::HashMap::new(),
            multiset_intersect_sources: std::collections::HashMap::new(),
            multiset_operand_sources: std::collections::HashMap::new(),
            derived_seq_views: std::collections::HashMap::new(),
            #[cfg(feature = "native-seq")]
            native_seq_shadows,
            #[cfg(feature = "native-strings")]
            native_string_view_shadows: std::collections::HashMap::new(),
            domain_terms,
            ground_pool: None,
            function_param_types: None,
            function_type_params: None,
            poly_context: None,
            choose_registry: None,
            dt_size_funcs: None,
            prophecy_registry: None,
            nat_cast_aliases: std::collections::HashMap::new(),
            map_dom_bridges: std::collections::HashMap::new(),
            map_subset_seen: false,
            pure_collection_cache: std::collections::HashMap::new(),
            euclid_div_mod_aliases: std::collections::HashMap::new(),
            euclid_guarded_lemma_pairs: std::collections::HashSet::new(),
            euclid_ufs: None,
        }
    }

    /// Whether to use Int (mathematical integer) arithmetic instead of bitvectors.
    /// True when inside Int-sorted quantifier bodies or when all variables are
    /// Sort::Int. Finite-BV quantifiers still increment `quantifier_depth` for
    /// side-channel suppression, but their depth is excluded here.
    pub(super) fn int_mode(&self) -> bool {
        self.quantifier_depth > self.bv_quantifier_depth || self.use_int_arithmetic
    }

    /// Returns the collected overflow checking predicates, consuming them.
    /// Each entry is a (description, predicate) pair where the predicate is TRUE
    /// when the operation does not overflow.
    pub fn take_overflow_checks(&mut self) -> Vec<OverflowCheck> {
        std::mem::take(&mut self.overflow_checks)
    }

    /// Returns the collected constant-folded overflow verdicts, consuming them.
    /// Each entry is a `(label, overflows)` pair; see
    /// `const_fold_overflow_verdicts`. Part of #2778.
    pub fn take_const_fold_overflow_verdicts(&mut self) -> Vec<ConstFoldOverflowCheck> {
        std::mem::take(&mut self.const_fold_overflow_verdicts)
    }

    /// Push a new quantifier scope for IR arithmetic context resolution.
    pub(super) fn push_quantifier_scope(
        &mut self,
        bound_vars: &[(String, crate::ir::TrustVcType)],
    ) {
        self.quantifier_scopes
            .push(QuantifierScope::from_bound_vars(bound_vars));
    }

    /// Pop the most recent quantifier scope.
    pub(super) fn pop_quantifier_scope(&mut self) {
        self.quantifier_scopes.pop();
    }

    /// Check if a Term is a quantifier-bound variable in any active scope.
    ///
    /// Used by `add_seq_index_bounds_check` to only skip bounds checks for
    /// bound variables (where the user's quantifier guard handles OOB), not
    /// for constant or free variable indices (#2231 Finding 1).
    pub(super) fn is_quantifier_bound_term(&self, term: Term) -> bool {
        self.quantifier_scopes
            .iter()
            .any(|scope| scope.bound_terms.contains(&term))
    }

    // Collection metadata helpers extracted to collection_state.rs (#2436).

    /// Resolve current quantifier wrapping semantics from explicit scope state.
    pub(super) fn current_quantifier_wrap_semantics(&self) -> Option<ArithSemantics> {
        self.quantifier_scopes
            .last()
            .and_then(QuantifierScope::wrap_semantics)
    }

    // Width inference and BV coercion helpers extracted to width_coercion.rs (#2436).
    // Array axiom helpers extracted to array_axioms.rs (#1979).
}
