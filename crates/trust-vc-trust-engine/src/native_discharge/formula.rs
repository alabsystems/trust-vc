// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `trust-types.Formula@1` -> a typed trust-vc boundary expression.
//!
//! # The payload is a typed AST, not an opaque string
//!
//! `ProofObligation.formula.payload` under schema `trust-types.Formula@1` is a
//! JSON document `{"formula": <Formula>, "source": {…}}`, where `<Formula>` is
//! `serde_json::to_value` of `trust_ir_contract::Formula` — serde's default
//! externally-tagged representation (`{"Add": [lhs, rhs]}`,
//! `{"Var": ["x", "Int"]}`, `{"Int": 1}`). A producer that could NOT parse the
//! clause fails closed to a source-only payload with no `formula` key at all;
//! that declines here rather than being read as an empty (vacuously true)
//! predicate.
//!
//! # The IR-owned codec is the only wire decoder
//!
//! The original payload is deserialized directly into `trust_ir_contract::Formula`
//! and `Sort`. This module only lowers that typed question into the engine's
//! expression language against the declared scope. Unknown canonical nodes still
//! decline; using the shared codec grants no proof or source authority.
//!
//! # Sorts on the wire carry no type information
//!
//! MEASURED in `trust_types::spec_parse`: the bare-clause parser that produces
//! these formulas has no types available and defaults EVERY leaf to
//! `Sort::Int`, mapping the clause word `result` to the MIR return place `_0`.
//! So a `u64` parameter arrives as `Var("x", Int)`. The real types come from the
//! trust-ir function signature, which is what the surrounding body lowering
//! declares. This decoder therefore resolves a variable's sort from the DECLARED
//! scope and treats a wire `Sort::Int` as "unspecified"; a wire sort that IS
//! specific (`Bool`, `BitVec(w)`) must agree with the declaration or the formula
//! declines. A name that is not in scope declines — there are no free variables.
//!
//! # Arithmetic on the wire is MATHEMATICAL, and this lane decides at a width
//!
//! `Add`/`Sub`/`Mul`/`Div`/`Rem` are unbounded-integer operations: the clause
//! parser types every leaf `Sort::Int` and the fleet lowers `Formula::Add` to
//! ay's `int_add`. This lane decides an obligation at the operand's DECLARED
//! machine width, where the two readings differ the moment the operation
//! overflows — `ensures result == x + 1` is FALSE at `x = u32::MAX` under the
//! clause's own semantics and TRUE at 32-bit wrapping width. So a mathematical
//! node over machine operands DECLINES here. It is not a hypothetical: the
//! producer's own lowering records a false `Proved` from the sibling mismatch
//! (truncating `%` vs Euclidean `mod`), and a `wrapping_add` body lowers to the
//! same plain `BinOp` this lane accepts, so there is no panic-freedom row to
//! catch it downstream. The `Bv*` family denotes the fixed-width operation and
//! is decided.
//!
//! # Fail-closed
//!
//! Every node this module does not model declines BY NAME. Nothing is ever
//! approximated, and in particular no unknown node is mapped to `true`: an
//! unmodelled conjunct silently read as `true` weakens an assumption harmlessly
//! but weakens an ASSERTION into a proof of nothing.

use super::{Decline, Scope, ScopeEntry};
use crate::{
    TrustCompareOp, TrustExpr, TrustLogicOp, TrustQuantifierBoundVar, TrustQuantifierKind,
    TrustSort,
};
use serde::Deserialize;
use serde_json::Value;
use trust_ir_contract::{formula_census::variant_name, Formula, Sort, Symbol};

/// The formula payload schemas this lane accepts.
///
/// One `const` so the decoder and any future producer-facing check cannot drift.
pub(crate) const ACCEPTED_FORMULA_SCHEMAS: &[&str] =
    &[crate::native_assertion_id::TRUST_TYPES_FORMULA_SCHEMA_V1];

/// THE ONE DOOR EVERY PRODUCER PREDICATE COMES THROUGH, and the seam that binds
/// the lane's reading of a formula to the reading its AUTHORITY checks.
///
/// # A `ProofFormula` carries TWO renderings, and they are independent fields
///
/// [`trust_ir::ProofFormula`] has both a `payload` (in the named `schema`) and
/// an optional `smtlib`. This lane decodes `payload` — that is what
/// [`formula_node`] reads and what [`FormulaDecoder`] lowers. But the authority
/// this lane leans on for the one fact it IMPORTS rather than derives — the
/// Clean-kernel re-check of a `Certified` row, run by the producer validator at
/// the input gate — grounds its goal from
/// `trust_ir::clean_expr_lowering::contract::predicate_text`, which is
/// `formula.smtlib.as_deref().unwrap_or(&formula.payload)`: it PREFERS `smtlib`.
///
/// Nothing upstream binds the two to each other. `clean_cic_lineage_digest`
/// hashes both fields, so a certificate's lineage still matches whatever pair
/// the producer chose; it never compares them. So a producer may publish a
/// closed tautology in `smtlib` for the kernel to discharge and an arbitrary
/// predicate in `payload` for this lane to assume, at a matching lineage and a
/// genuinely kernel-checked certificate. MEASURED (round 7, probe R7-P2):
/// `smtlib = "(>= _0 0)"` with `payload = {"Ge":[{"Var":["_0","Int"]},{"Int":100}]}`
/// mints a real certificate from trust-ir's own miner, and the lane's lowered
/// assumption carries the `100`.
///
/// # The rule
///
/// A predicate is decoded only when there is ONE rendering: `smtlib` absent, or
/// `smtlib` byte-identical to `payload` (which is how `ProofFormula::smtlib2`
/// builds a row, and the shape in which the kernel's goal and this lane's
/// assumption are the same object). Two disagreeing renderings DECLINE.
///
/// This is deliberately a check on BYTES, not a semantic comparison: this crate
/// has no SMT-LIB reader, and a "close enough" comparison of two notations is
/// precisely the approximation that would put the hole back. It applies to every
/// predicate the lane reads — the obligation it DECIDES, the def-site `requires`
/// it ASSUMES, and an imported callee `ensures` — because the divergence is a
/// misidentification of the formula, not a property of one role.
///
/// `sort` is the third producer-supplied rendering field. It is NOT read here
/// and is authority for nothing: `predicate_text` and `contract_goal` never
/// consult it, and this decoder resolves every variable's sort from the DECLARED
/// trust-ir scope (see the module docs). It is recorded in the enumeration so a
/// future reader does not have to re-derive that.
pub(crate) fn decode_predicate(formula: &trust_ir::ProofFormula) -> Result<Formula, Decline> {
    if let Some(smtlib) = formula.smtlib.as_deref() {
        if smtlib != formula.payload {
            return Err(Decline::new(format!(
                "formula carries two renderings that are not the same bytes: `smtlib` is                  {smtlib:?} while `payload` (schema `{}`) is {:?}. The Clean-kernel re-check                  that is this lane's authority for an imported contract grounds its goal from                  `smtlib` (trust-ir's `predicate_text` prefers it) and this lane decodes                  `payload`; nothing upstream binds the two, so admitting the row would let a                  kernel-checked certificate stand for a DIFFERENT formula than the one assumed",
                formula.schema, formula.payload
            )));
        }
    }
    formula_node(&formula.schema, &formula.payload)
}

/// Pull the `formula` AST out of a `ProofFormula` payload.
///
/// PRIVATE ON PURPOSE: every caller in the lane goes through
/// [`decode_predicate`], which additionally binds `payload` to the `smtlib`
/// rendering the kernel checks. Taking the two strings apart here would let a
/// caller re-open that gap.
fn formula_node(schema: &str, payload: &str) -> Result<Formula, Decline> {
    if !ACCEPTED_FORMULA_SCHEMAS.contains(&schema) {
        return Err(Decline::new(format!(
            "unmodelled formula schema `{schema}`: the discharge lane accepts {}",
            ACCEPTED_FORMULA_SCHEMAS.join(", ")
        )));
    }
    // Deserialize the formula directly from the original bytes. An intermediate
    // Value would discard duplicate formula/tag fields before the typed codec
    // can reject them. Opaque metadata still uses Value's bounded JSON reader.
    #[derive(Deserialize)]
    struct Payload {
        formula: Option<Formula>,
        #[serde(flatten)]
        _metadata: std::collections::BTreeMap<String, Value>,
    }
    let document: Payload = serde_json::from_str(payload)
        .map_err(|error| Decline::new(format!("formula payload is not canonical JSON: {error}")))?;
    document.formula.ok_or_else(|| {
        Decline::new(
            "formula payload carries no `formula` node: the producer failed closed to \
             source-only metadata, so this obligation has no machine-readable predicate",
        )
    })
}

/// Which arithmetic an arithmetic NODE denotes.
///
/// MEASURED in the producer: `trust_types::spec_parse` types every clause leaf
/// `Sort::Int`, and `trust_types::ay_bridge` lowers `Formula::Add` to ay's
/// `int_add` — mathematical integer arithmetic on unbounded integers. The
/// `Bv*` nodes are the other reading, and they say so in their own name.
///
/// The distinction is load-bearing, not pedantic: that same producer file
/// records a FALSE `Proved` (`#[ensures(result >= 0)] fn f(x: i32) -> i32
/// { x % 256 }`) caused by exactly this class of Rust-vs-mathematics mismatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArithReading {
    /// Unbounded integer arithmetic: `Add`, `Sub`, `Mul`, `Div`, `Rem`.
    Mathematical,
    /// Fixed-width wrapping arithmetic: the `Bv*` family.
    MachineWidth,
}

/// Lowers `trust-types.Formula@1` nodes against a declared variable scope.
pub(crate) struct FormulaDecoder<'a> {
    scope: &'a Scope,
    /// Quantifier binders currently in scope, innermost last.
    bound: Vec<(String, TrustSort)>,
}

impl<'a> FormulaDecoder<'a> {
    pub(crate) fn new(scope: &'a Scope) -> Self {
        Self {
            scope,
            bound: Vec::new(),
        }
    }

    /// Lower a whole obligation predicate, which must have `Bool` sort.
    pub(crate) fn lower_predicate(&mut self, node: &Formula) -> Result<TrustExpr, Decline> {
        self.lower(node, Some(&TrustSort::Bool))
    }

    /// Resolve a wire name to what the unit declares for it.
    ///
    /// A quantifier binder shadows the function scope and emits under its own
    /// name; a function-scope name emits under the unit's variable name for it,
    /// which is NOT always the wire name: a callee's contract is lowered in a
    /// scope that maps the callee's own parameter names onto the caller's
    /// argument variables.
    fn declared(&self, name: &str) -> Option<ScopeEntry> {
        self.bound
            .iter()
            .rev()
            .find_map(|(bound, sort)| {
                (bound == name).then(|| ScopeEntry::new(bound.clone(), sort.clone()))
            })
            .or_else(|| self.scope.get(name).cloned())
    }

    /// The sort a node has WITHOUT context, or `None` for a bare numeric
    /// literal (whose sort is decided by its sibling or by the expected sort).
    fn infer(&self, node: &Formula) -> Option<TrustSort> {
        use Formula::*;
        match node {
            Bool(_) | Not(_) | And(_) | Or(_) | Implies(..) | Eq(..) | Lt(..) | Le(..) | Gt(..)
            | Ge(..) | BvULt(..) | BvULe(..) | BvSLt(..) | BvSLe(..) | Forall(..) | Exists(..) => {
                Some(TrustSort::Bool)
            }
            Var(name, _) => self.declared(name).map(|entry| entry.sort),
            SymVar(name, _) => self.declared(name.as_str()).map(|entry| entry.sort),
            Add(lhs, rhs)
            | Sub(lhs, rhs)
            | Mul(lhs, rhs)
            | Div(lhs, rhs)
            | Rem(lhs, rhs)
            | BvAdd(lhs, rhs, _)
            | BvSub(lhs, rhs, _)
            | BvMul(lhs, rhs, _)
            | BvUDiv(lhs, rhs, _)
            | BvSDiv(lhs, rhs, _)
            | BvURem(lhs, rhs, _)
            | BvSRem(lhs, rhs, _) => self.infer(lhs).or_else(|| self.infer(rhs)),
            Ite(_, yes, no) => self.infer(yes).or_else(|| self.infer(no)),
            _ => None,
        }
    }

    fn lower(
        &mut self,
        node: &Formula,
        expected: Option<&TrustSort>,
    ) -> Result<TrustExpr, Decline> {
        use Formula::*;
        let tag = variant_name(node);
        match node {
            Bool(value) => {
                self.expect_sort(expected, &TrustSort::Bool, "boolean literal")?;
                Ok(TrustExpr::bool_literal(*value))
            }
            Int(value) => self.int_literal(*value, expected),
            UInt(value) => {
                let value = i128::try_from(*value).map_err(|_|
                    Decline::new("unsigned literal exceeds i128 and cannot be represented"))?;
                self.int_literal(value, expected)
            }
            BitVec { value, width } => match expected {
                Some(TrustSort::BitVector { width: declared, .. }) if declared == width =>
                    self.int_literal(*value, expected),
                Some(other) => Err(Decline::new(format!(
                    "bitvector literal of width {width} where {} is expected", other.display_label()))),
                None => Err(Decline::new(format!(
                    "bitvector literal of width {width} in a position with no expected sort: its signedness is not recoverable"))),
            },
            Var(name, wire) => self.variable(name, wire, expected),
            SymVar(name, wire) => self.variable(name.as_str(), wire, expected),
            Not(body) => {
                let inner = self.lower(body, Some(&TrustSort::Bool))?;
                self.expect_sort(expected, &TrustSort::Bool, "logical negation")?;
                Ok(TrustExpr::not(inner))
            }
            And(items) => self.connective(items, TrustLogicOp::And, expected),
            Or(items) => self.connective(items, TrustLogicOp::Or, expected),
            Implies(lhs, rhs) => {
                let premise = self.lower(lhs, Some(&TrustSort::Bool))?;
                let conclusion = self.lower(rhs, Some(&TrustSort::Bool))?;
                self.expect_sort(expected, &TrustSort::Bool, "implication")?;
                Ok(TrustExpr::implies(premise, conclusion))
            }
            Eq(lhs, rhs) => self.comparison(lhs, rhs, TrustCompareOp::Eq, tag, None, expected),
            Lt(lhs, rhs) => self.comparison(lhs, rhs, TrustCompareOp::Lt, tag, None, expected),
            Le(lhs, rhs) => self.comparison(lhs, rhs, TrustCompareOp::Le, tag, None, expected),
            Gt(lhs, rhs) => self.comparison(lhs, rhs, TrustCompareOp::Gt, tag, None, expected),
            Ge(lhs, rhs) => self.comparison(lhs, rhs, TrustCompareOp::Ge, tag, None, expected),
            BvULt(lhs, rhs, width) => self.bv_comparison(lhs, rhs, *width, TrustCompareOp::Lt, tag, false, expected),
            BvULe(lhs, rhs, width) => self.bv_comparison(lhs, rhs, *width, TrustCompareOp::Le, tag, false, expected),
            BvSLt(lhs, rhs, width) => self.bv_comparison(lhs, rhs, *width, TrustCompareOp::Lt, tag, true, expected),
            BvSLe(lhs, rhs, width) => self.bv_comparison(lhs, rhs, *width, TrustCompareOp::Le, tag, true, expected),
            Add(lhs, rhs) => self.arith(lhs, rhs, crate::TrustArithOp::Add, tag, None, expected, ArithReading::Mathematical),
            Sub(lhs, rhs) => self.arith(lhs, rhs, crate::TrustArithOp::Sub, tag, None, expected, ArithReading::Mathematical),
            Mul(lhs, rhs) => self.arith(lhs, rhs, crate::TrustArithOp::Mul, tag, None, expected, ArithReading::Mathematical),
            Div(lhs, rhs) => self.arith(lhs, rhs, crate::TrustArithOp::Div, tag, None, expected, ArithReading::Mathematical),
            Rem(lhs, rhs) => self.arith(lhs, rhs, crate::TrustArithOp::Rem, tag, None, expected, ArithReading::Mathematical),
            BvAdd(lhs, rhs, width) => self.bv_arith(lhs, rhs, *width, crate::TrustArithOp::Add, tag, None, expected),
            BvSub(lhs, rhs, width) => self.bv_arith(lhs, rhs, *width, crate::TrustArithOp::Sub, tag, None, expected),
            BvMul(lhs, rhs, width) => self.bv_arith(lhs, rhs, *width, crate::TrustArithOp::Mul, tag, None, expected),
            BvUDiv(lhs, rhs, width) => self.bv_arith(lhs, rhs, *width, crate::TrustArithOp::Div, tag, Some(false), expected),
            BvSDiv(lhs, rhs, width) => self.bv_arith(lhs, rhs, *width, crate::TrustArithOp::Div, tag, Some(true), expected),
            BvURem(lhs, rhs, width) => self.bv_arith(lhs, rhs, *width, crate::TrustArithOp::Rem, tag, Some(false), expected),
            BvSRem(lhs, rhs, width) => self.bv_arith(lhs, rhs, *width, crate::TrustArithOp::Rem, tag, Some(true), expected),
            Ite(cond, yes, no) => self.ite(cond, yes, no, expected),
            Forall(bindings, body) => self.quantifier(bindings, body, TrustQuantifierKind::Forall, tag, expected),
            Exists(bindings, body) => self.quantifier(bindings, body, TrustQuantifierKind::Exists, tag, expected),
            _ => Err(Decline::new(format!("unmodelled `trust-types.Formula@1` node `{tag}`"))),
        }
    }

    fn int_literal(&self, value: i128, expected: Option<&TrustSort>) -> Result<TrustExpr, Decline> {
        let sort = expected.ok_or_else(|| {
            Decline::new(
                "integer literal in a position with no expected sort: its width and signedness \
                 are not recoverable from the formula alone",
            )
        })?;
        match sort {
            TrustSort::BitVector { signed, width } => {
                if !signed && value < 0 {
                    return Err(Decline::new(format!(
                        "negative integer literal {value} where u{width} is expected"
                    )));
                }
                Ok(TrustExpr::int_literal(value, sort.clone()))
            }
            TrustSort::MathInt | TrustSort::Nat => Ok(TrustExpr::int_literal(value, sort.clone())),
            other => Err(Decline::new(format!(
                "integer literal where {} is expected",
                other.display_label()
            ))),
        }
    }

    fn variable(
        &self,
        name: &str,
        wire: &Sort,
        expected: Option<&TrustSort>,
    ) -> Result<TrustExpr, Decline> {
        let entry = self.declared(name).ok_or_else(|| unknown_variable(name))?;
        check_wire_sort(wire, &entry.sort, name)?;
        if let Some(expected) = expected {
            if *expected != entry.sort {
                return Err(Decline::new(format!(
                    "variable `{name}` is {} but {} is expected here",
                    entry.sort.display_label(),
                    expected.display_label()
                )));
            }
        }
        Ok(TrustExpr::variable(entry.emit, entry.sort))
    }

    fn connective(
        &mut self,
        items: &[Formula],
        op: TrustLogicOp,
        expected: Option<&TrustSort>,
    ) -> Result<TrustExpr, Decline> {
        self.expect_sort(
            expected,
            &TrustSort::Bool,
            match op {
                TrustLogicOp::And => "conjunction",
                TrustLogicOp::Or => "disjunction",
            },
        )?;
        // The identity of an empty n-ary connective: `And([])` is `true`,
        // `Or([])` is `false`. These are the SMT-LIB identities, not a
        // convenience: reading `And([])` as anything else would change meaning,
        // and reading `Or([])` as `true` would prove an empty disjunction.
        let mut items = items.iter();
        let Some(first) = items.next() else {
            return Ok(TrustExpr::bool_literal(matches!(op, TrustLogicOp::And)));
        };
        let mut expr = self.lower(first, Some(&TrustSort::Bool))?;
        for item in items {
            let next = self.lower(item, Some(&TrustSort::Bool))?;
            expr = TrustExpr::logic(op, expr, next);
        }
        Ok(expr)
    }

    fn comparison(
        &mut self,
        lhs: &Formula,
        rhs: &Formula,
        op: TrustCompareOp,
        tag: &str,
        require_signed: Option<bool>,
        expected: Option<&TrustSort>,
    ) -> Result<TrustExpr, Decline> {
        let operand = self.operand_sort(
            &lhs,
            &rhs,
            None,
            &format!("`{tag}` compares two literals, so the comparison's sort is not recoverable"),
        )?;
        if !matches!(op, TrustCompareOp::Eq | TrustCompareOp::Ne)
            && !matches!(
                operand,
                TrustSort::BitVector { .. } | TrustSort::MathInt | TrustSort::Nat
            )
        {
            return Err(Decline::new(format!(
                "`{tag}` orders {} operands, which the discharge lane does not model",
                operand.display_label()
            )));
        }
        if let Some(require_signed) = require_signed {
            require_bitvector_signedness(&operand, require_signed, tag)?;
        }
        let left = self.lower(&lhs, Some(&operand))?;
        let right = self.lower(&rhs, Some(&operand))?;
        self.expect_sort(expected, &TrustSort::Bool, tag)?;
        Ok(TrustExpr::compare(op, left, right))
    }

    fn bv_comparison(
        &mut self,
        lhs: &Formula,
        rhs: &Formula,
        width: u32,
        op: TrustCompareOp,
        tag: &str,
        signed: bool,
        expected: Option<&TrustSort>,
    ) -> Result<TrustExpr, Decline> {
        let result = self.comparison(lhs, rhs, op, tag, Some(signed), expected)?;
        self.check_width(lhs, rhs, width, tag)?;
        Ok(result)
    }

    fn arith(
        &mut self,
        lhs: &Formula,
        rhs: &Formula,
        op: crate::TrustArithOp,
        tag: &str,
        require_signed: Option<bool>,
        expected: Option<&TrustSort>,
        reading: ArithReading,
    ) -> Result<TrustExpr, Decline> {
        let sort = self.operand_sort(
            &lhs,
            &rhs,
            expected,
            &format!("`{tag}` combines two literals, so the result sort is not recoverable"),
        )?;
        if !matches!(
            sort,
            TrustSort::BitVector { .. } | TrustSort::MathInt | TrustSort::Nat
        ) {
            return Err(Decline::new(format!(
                "`{tag}` over {} operands, which the discharge lane does not model",
                sort.display_label()
            )));
        }
        if let Some(require_signed) = require_signed {
            require_bitvector_signedness(&sort, require_signed, tag)?;
        }
        // SOUNDNESS: a MATHEMATICAL node over MACHINE operands is refused.
        if matches!(reading, ArithReading::Mathematical)
            && matches!(sort, TrustSort::BitVector { .. })
        {
            return Err(Decline::new(format!(
                "`{tag}` over {} operands: a `trust-types.Formula@1` `{tag}` is MATHEMATICAL \
                 integer arithmetic — the clause parser types every leaf `Sort::Int` and the \
                 fleet lowers it to ay's `int_*` — but this lane decides the obligation at the \
                 operand's declared machine width, and the two readings part company as soon as \
                 the operation overflows (and, for `Div`/`Rem`, on sign). Deciding it here would \
                 prove a DIFFERENT predicate than the clause spells, so the lane declines; a \
                 machine-width `Bv{tag}`-family node says what it means and is decided",
                sort.display_label()
            )));
        }
        if let Some(expected) = expected {
            if *expected != sort {
                return Err(Decline::new(format!(
                    "`{tag}` produces {} but {} is expected here",
                    sort.display_label(),
                    expected.display_label()
                )));
            }
        }
        let left = self.lower(&lhs, Some(&sort))?;
        let right = self.lower(&rhs, Some(&sort))?;
        if matches!(reading, ArithReading::Mathematical)
            && sort == TrustSort::MathInt
            && matches!(op, crate::TrustArithOp::Div | crate::TrustArithOp::Rem)
        {
            if matches!(rhs, Formula::Int(0) | Formula::UInt(0)) {
                return Err(Decline::new("canonical integer division/remainder by zero"));
            }
            return truncated_math_arithmetic(op, left, right);
        }
        Ok(TrustExpr::arith(op, left, right, sort))
    }

    fn bv_arith(
        &mut self,
        lhs: &Formula,
        rhs: &Formula,
        width: u32,
        op: crate::TrustArithOp,
        tag: &str,
        require_signed: Option<bool>,
        expected: Option<&TrustSort>,
    ) -> Result<TrustExpr, Decline> {
        // A `Bv*` node DENOTES the fixed-width operation, so deciding it at that
        // width is what it means, not an approximation of something else.
        let result = self.arith(
            lhs,
            rhs,
            op,
            tag,
            require_signed,
            expected,
            ArithReading::MachineWidth,
        )?;
        self.check_width(lhs, rhs, width, tag)?;
        Ok(result)
    }

    /// `Ite` at `Bool` result sort only, rewritten to the equivalent
    /// `(c => t) && (!c => e)`.
    ///
    /// trust-vc's boundary expression has no conditional node, and the rewrite
    /// is only sound when the branches are propositions — for a value-sorted
    /// `Ite` there is nothing to rewrite to, so it declines.
    fn ite(
        &mut self,
        cond: &Formula,
        yes: &Formula,
        no: &Formula,
        expected: Option<&TrustSort>,
    ) -> Result<TrustExpr, Decline> {
        let result = self
            .infer(yes)
            .or_else(|| self.infer(no))
            .or_else(|| expected.cloned());
        if result.as_ref() != Some(&TrustSort::Bool) {
            return Err(Decline::new(format!(
                "`Ite` at {} result sort: the boundary expression has no conditional node, \
                 so only a Bool-sorted conditional can be rewritten",
                result
                    .as_ref()
                    .map_or_else(|| "an unrecoverable".to_string(), TrustSort::display_label)
            )));
        }
        let cond = self.lower(cond, Some(&TrustSort::Bool))?;
        let then_branch = self.lower(yes, Some(&TrustSort::Bool))?;
        let else_branch = self.lower(no, Some(&TrustSort::Bool))?;
        Ok(TrustExpr::logic(
            TrustLogicOp::And,
            TrustExpr::implies(cond.clone(), then_branch),
            TrustExpr::implies(TrustExpr::not(cond), else_branch),
        ))
    }

    fn quantifier(
        &mut self,
        bindings: &[(Symbol, Sort)],
        body: &Formula,
        kind: TrustQuantifierKind,
        tag: &str,
        expected: Option<&TrustSort>,
    ) -> Result<TrustExpr, Decline> {
        if bindings.is_empty() {
            return Err(Decline::new(format!("`{tag}` declares no bound variable")));
        }
        let mut bound_vars = Vec::new();
        let depth = self.bound.len();
        for (name, wire) in bindings {
            let name = name.as_str();
            let sort = binder_sort(wire)?;
            bound_vars.push(TrustQuantifierBoundVar::new(name, sort.clone()));
            self.bound.push((name.to_string(), sort));
        }
        let lowered = self.lower(body, Some(&TrustSort::Bool));
        self.bound.truncate(depth);
        let inner = lowered?;
        self.expect_sort(expected, &TrustSort::Bool, tag)?;
        Ok(TrustExpr::quantifier(kind, bound_vars, inner))
    }

    /// The sort a binary node's operands share.
    ///
    /// When neither side is inferable, the honest reason is usually that one of
    /// them is a variable the function does not declare — report THAT rather
    /// than "two literals", which points at the wrong thing and reads as a
    /// limitation instead of a rejected formula.
    fn operand_sort(
        &self,
        lhs: &Formula,
        rhs: &Formula,
        expected: Option<&TrustSort>,
        otherwise: &str,
    ) -> Result<TrustSort, Decline> {
        if let Some(sort) = self
            .infer(lhs)
            .or_else(|| self.infer(rhs))
            .or_else(|| expected.cloned())
        {
            return Ok(sort);
        }
        for side in [lhs, rhs] {
            let name = match side {
                Formula::Var(name, _) => Some(name.as_str()),
                Formula::SymVar(name, _) => Some(name.as_str()),
                _ => None,
            };
            if let Some(name) = name {
                if self.declared(name).is_none() {
                    return Err(unknown_variable(name));
                }
            }
        }
        Err(Decline::new(otherwise.to_string()))
    }

    fn expect_sort(
        &self,
        expected: Option<&TrustSort>,
        actual: &TrustSort,
        what: &str,
    ) -> Result<(), Decline> {
        match expected {
            Some(expected) if expected != actual => Err(Decline::new(format!(
                "{what} has {} sort but {} is expected here",
                actual.display_label(),
                expected.display_label()
            ))),
            _ => Ok(()),
        }
    }

    /// A `Bv*` node names its operand width; the sort resolved from the declared
    /// scope must agree, or the formula is about a different value than the
    /// function declares.
    fn check_width(
        &self,
        lhs: &Formula,
        rhs: &Formula,
        width: u32,
        tag: &str,
    ) -> Result<(), Decline> {
        let sort = self.operand_sort(
            &lhs,
            &rhs,
            None,
            &format!("`{tag}` operands have no recoverable sort"),
        )?;
        match sort {
            TrustSort::BitVector { width: actual, .. } if actual == width => Ok(()),
            other => Err(Decline::new(format!(
                "`{tag}` declares width {width} but its operands are {}",
                other.display_label()
            ))),
        }
    }
}

// This is an untrusted expression-materialization budget, not a logical
// premise. Check the complete expansion BEFORE cloning operands so nested
// divisions/remainders cannot allocate an exponential tree.
const MAX_TRUNCATED_EXPANSION_NODES: usize = 4096;

fn expression_nodes(expr: &TrustExpr) -> Option<usize> {
    let mut pending = vec![expr];
    let mut count = 0usize;
    while let Some(expr) = pending.pop() {
        count = count.checked_add(1)?;
        if count > MAX_TRUNCATED_EXPANSION_NODES {
            return None;
        }
        match expr {
            TrustExpr::BoolLiteral { .. }
            | TrustExpr::IntLiteral { .. }
            | TrustExpr::Variable { .. }
            | TrustExpr::Old { .. } => {}
            TrustExpr::Arith { left, right, .. }
            | TrustExpr::Compare { left, right, .. }
            | TrustExpr::Logic { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            TrustExpr::Not { expr } | TrustExpr::Cast { expr, .. } => pending.push(expr),
            TrustExpr::Implies {
                premise,
                conclusion,
            } => {
                pending.push(premise);
                pending.push(conclusion);
            }
            TrustExpr::Ite {
                condition,
                then_expr,
                else_expr,
                ..
            } => {
                pending.push(condition);
                pending.push(then_expr);
                pending.push(else_expr);
            }
            TrustExpr::Call { args, .. } => pending.extend(args),
            TrustExpr::Quantifier { body, triggers, .. } => {
                pending.push(body);
                if let Some(triggers) = triggers {
                    for group in triggers {
                        pending.extend(group);
                    }
                }
            }
        }
    }
    Some(count)
}

fn truncated_math_arithmetic(
    op: crate::TrustArithOp,
    left: TrustExpr,
    right: TrustExpr,
) -> Result<TrustExpr, Decline> {
    use crate::TrustArithOp::{Div, Rem, Sub};
    let budget_error =
        || Decline::new("canonical truncated arithmetic expansion exceeds 4096 nodes");
    let l = expression_nodes(&left).ok_or_else(budget_error)?;
    let r = expression_nodes(&right).ok_or_else(budget_error)?;
    let nodes = if op == Div {
        l.checked_mul(4)
            .and_then(|n| r.checked_mul(3).and_then(|r| n.checked_add(r)))
            .and_then(|n| n.checked_add(11))
    } else {
        l.checked_mul(3)
            .and_then(|n| r.checked_mul(2).and_then(|r| n.checked_add(r)))
            .and_then(|n| n.checked_add(9))
    };
    if nodes.is_none_or(|n| n > MAX_TRUNCATED_EXPANSION_NODES) {
        return Err(budget_error());
    }
    let int = TrustSort::MathInt;
    let zero = || TrustExpr::int_literal(0, int.clone());
    // Exactly canonical Formula's truncating remainder:
    // ite(a >= 0, mod(a,b), -mod(-a,b)). Each mod is Euclidean in
    // TrustVc's MathInt language; Verus's existing operator stays unchanged.
    let rem = TrustExpr::ite(
        TrustExpr::compare(TrustCompareOp::Ge, left.clone(), zero()),
        TrustExpr::arith(Rem, left.clone(), right.clone(), int.clone()),
        TrustExpr::arith(
            Sub,
            zero(),
            TrustExpr::arith(
                Rem,
                TrustExpr::arith(Sub, zero(), left.clone(), int.clone()),
                right.clone(),
                int.clone(),
            ),
            int.clone(),
        ),
        int.clone(),
    );
    if op == Div {
        // a - trem(a,b) is exactly divisible by every nonzero b, so the
        // existing Euclidean division agrees with the canonical quotient.
        Ok(TrustExpr::arith(
            Div,
            TrustExpr::arith(Sub, left, rem, int.clone()),
            right,
            int,
        ))
    } else {
        Ok(rem)
    }
}

/// `Sort` for a quantifier binder.
///
/// A binder's sort comes ONLY from the wire, and `Sort::BitVec(w)` does not say
/// whether it is signed — which decides what `<` means. There is no declaration
/// to resolve it against, so a bitvector binder declines instead of guessing.
fn binder_sort(wire: &Sort) -> Result<TrustSort, Decline> {
    match wire {
        Sort::Bool => Ok(TrustSort::Bool),
        Sort::Int => Ok(TrustSort::MathInt),
        Sort::BitVec(width) => Err(Decline::new(format!(
            "quantifier binder of sort BitVec({width}): signedness is not on the wire, \
             and it decides the meaning of every ordered comparison over the binder"
        ))),
        other => Err(Decline::new(format!(
            "unmodelled quantifier binder sort `{other:?}`"
        ))),
    }
}

/// Is the wire sort consistent with what the function declares for `name`?
fn check_wire_sort(wire: &Sort, declared: &TrustSort, name: &str) -> Result<(), Decline> {
    match wire {
        // The bare-clause parser defaults every leaf to `Sort::Int`, so `Int`
        // carries no claim at all. The declaration wins.
        Sort::Int => Ok(()),
        Sort::Bool if matches!(declared, TrustSort::Bool) => Ok(()),
        Sort::BitVec(width) if matches!(declared, TrustSort::BitVector { width: w, .. } if w == width) => {
            Ok(())
        }
        Sort::BitVec(32) if matches!(declared, TrustSort::Char) => Ok(()),
        other => Err(Decline::new(format!(
            "formula gives variable `{name}` sort {} but the function declares it {}",
            sort_label(other),
            declared.display_label()
        ))),
    }
}

/// The one message for "the formula names something the function does not bind".
fn unknown_variable(name: &str) -> Decline {
    Decline::new(format!(
        "formula names variable `{name}`, which is not in the function's scope \
         (parameters, SSA values, quantifier binders and the return place `_0`)"
    ))
}

fn sort_label(sort: &Sort) -> String {
    match sort {
        Sort::Bool => "Bool".into(),
        Sort::Int => "Int".into(),
        Sort::BitVec(width) => format!("BitVec({width})"),
        other => format!("{other:?}"),
    }
}

fn require_bitvector_signedness(sort: &TrustSort, signed: bool, tag: &str) -> Result<(), Decline> {
    match sort {
        TrustSort::BitVector {
            signed: actual,
            width,
        } if *actual == signed => {
            let _ = width;
            Ok(())
        }
        other => Err(Decline::new(format!(
            "`{tag}` is a {} operation but its operands are {}; trust-vc carries signedness on \
             the sort, so this cannot be expressed without changing what is asserted",
            if signed { "signed" } else { "unsigned" },
            other.display_label()
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TrustArithOp;
    use trust_ir_contract::{Formula, Sort};

    /// Wrap a REAL `trust_ir_contract::Formula` the way the producer does.
    ///
    /// The actual producer type owns serialization and deserialization; the
    /// adapter only decides whether it can lower the decoded question.
    fn payload(formula: &Formula) -> String {
        serde_json::json!({
            "formula": serde_json::to_value(formula).expect("Formula serializes"),
            "source": {
                "source_id": "rust:probe.rs::inc",
                "assertion_id": "rust-assertion:1",
                "native_assertion_id": 1,
                "span": { "file": 0, "line_start": 1, "col_start": 1, "line_end": 1, "col_end": 2 },
            },
        })
        .to_string()
    }

    fn scope() -> Scope {
        [
            ("x", TrustSort::unsigned(64)),
            ("s", TrustSort::signed(32)),
            ("b", TrustSort::Bool),
            ("_0", TrustSort::unsigned(64)),
        ]
        .into_iter()
        .map(|(name, sort)| (name.to_string(), ScopeEntry::new(name.to_string(), sort)))
        .collect()
    }

    fn lower(formula: &Formula) -> Result<TrustExpr, Decline> {
        let scope = scope();
        let node = formula_node("trust-types.Formula@1", &payload(formula))?;
        FormulaDecoder::new(&scope).lower_predicate(&node)
    }

    fn var(name: &str) -> Formula {
        // The bare-clause parser defaults EVERY leaf to `Sort::Int`. Using it
        // here is not a convenience — it is the shape the producer emits.
        Formula::Var(name.to_string(), Sort::Int)
    }

    /// `ensures result == x + 1` on `u64`, exactly as the clause parser spells
    /// it: `result` is the MIR return place `_0`, and every leaf sort is `Int`.
    ///
    /// It DECLINES, and this test is the record of why. An earlier revision
    /// lowered the `Add` at the operand's declared machine width; adversarial
    /// review then proved a FALSE `Discharged` with it — `ensures result == x +
    /// 1` for `fn inc(x: u32) -> u32 { x + 1 }` certified at `x = u32::MAX`,
    /// where the clause's own (mathematical) value is 2^32 and the program
    /// returns 0. A `wrapping_add` body lowers to the same plain `BinOp` this
    /// lane accepts, so no panic-freedom row would ever have caught it.
    #[test]
    fn the_canonical_scalar_postcondition_declines_at_a_machine_width() {
        let formula = Formula::Eq(
            Box::new(var("_0")),
            Box::new(Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)))),
        );
        let decline = lower(&formula).expect_err("mathematical `Add` over u64 operands");
        assert!(decline.reason().contains("MATHEMATICAL"), "{decline}");
        assert!(decline.reason().contains("u64"), "{decline}");

        // Every mathematical arithmetic node, not just `Add`.
        for (name, node) in [
            (
                "Sub",
                Formula::Sub(Box::new(var("x")), Box::new(Formula::Int(1))),
            ),
            (
                "Mul",
                Formula::Mul(Box::new(var("x")), Box::new(Formula::Int(2))),
            ),
            (
                "Div",
                Formula::Div(Box::new(var("x")), Box::new(Formula::Int(2))),
            ),
            (
                "Rem",
                Formula::Rem(Box::new(var("x")), Box::new(Formula::Int(2))),
            ),
        ] {
            let formula = Formula::Eq(Box::new(var("_0")), Box::new(node));
            let decline = lower(&formula).expect_err("mathematical arithmetic over u64");
            assert!(
                decline.reason().contains("MATHEMATICAL"),
                "`{name}` must decline at a machine width: {decline}"
            );
        }

        // The node that DENOTES the fixed-width operation is decided at that
        // width, because that is what it means — the decline is about the
        // reading, not about arithmetic.
        let machine = Formula::Eq(
            Box::new(var("_0")),
            Box::new(Formula::BvAdd(
                Box::new(var("x")),
                Box::new(Formula::Int(1)),
                64,
            )),
        );
        let lowered = lower(&machine).expect("a `BvAdd` at the declared width lowers");
        assert_eq!(
            lowered,
            TrustExpr::compare(
                TrustCompareOp::Eq,
                TrustExpr::variable("_0", TrustSort::unsigned(64)),
                TrustExpr::arith(
                    TrustArithOp::Add,
                    TrustExpr::variable("x", TrustSort::unsigned(64)),
                    TrustExpr::int_literal(1, TrustSort::unsigned(64)),
                    TrustSort::unsigned(64),
                ),
            )
        );
        // And it survives the lowering the engine actually verifies over.
        lowered
            .to_trust_vc_expr()
            .expect("the boundary expression lowers to trust-vc IR");

        // Mathematical arithmetic over a MATHEMATICAL operand is untouched: a
        // quantifier binder carries the wire's own `Sort::Int`, and there the
        // two readings are the same reading.
        let quantified = Formula::Forall(
            vec![("i".into(), Sort::Int)],
            Box::new(Formula::Ge(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("i".to_string(), Sort::Int)),
                    Box::new(Formula::Int(1)),
                )),
                Box::new(Formula::Var("i".to_string(), Sort::Int)),
            )),
        );
        let lowered = lower(&quantified).expect("`Add` over unbounded integers lowers");
        assert_eq!(
            lowered,
            TrustExpr::forall(
                vec![TrustQuantifierBoundVar::new("i", TrustSort::MathInt)],
                TrustExpr::compare(
                    TrustCompareOp::Ge,
                    TrustExpr::arith(
                        TrustArithOp::Add,
                        TrustExpr::variable("i", TrustSort::MathInt),
                        TrustExpr::int_literal(1, TrustSort::MathInt),
                        TrustSort::MathInt,
                    ),
                    TrustExpr::variable("i", TrustSort::MathInt),
                ),
            ),
            "quantified mathematical arithmetic must retain its binder and unbounded sort"
        );
    }

    /// The wire sort is the parser's `Int` placeholder for every leaf, so the
    /// DECLARED type is what decides width and signedness. Getting this wrong in
    /// the other direction (trusting the wire) would verify `x + 1` as unbounded
    /// integer arithmetic on a `u64`, which cannot overflow — and would prove a
    /// postcondition that is false in the program.
    #[test]
    fn declared_types_decide_width_and_signedness_not_the_wire() {
        let formula = Formula::Lt(Box::new(var("s")), Box::new(Formula::Int(-1)));
        let lowered = lower(&formula).expect("i32 comparison lowers");
        assert_eq!(
            lowered,
            TrustExpr::compare(
                TrustCompareOp::Lt,
                TrustExpr::variable("s", TrustSort::signed(32)),
                TrustExpr::int_literal(-1, TrustSort::signed(32)),
            )
        );
        // The same literal against the unsigned declaration is refused, not
        // wrapped to 2^64-1.
        let unsigned = Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(-1)));
        let decline = lower(&unsigned).expect_err("negative literal, unsigned declaration");
        assert!(decline.reason().contains("negative"), "{decline}");
    }

    #[test]
    fn a_specific_wire_sort_must_agree_with_the_declaration() {
        let formula = Formula::Eq(
            Box::new(Formula::Var("x".to_string(), Sort::BitVec(32))),
            Box::new(Formula::Int(0)),
        );
        let decline = lower(&formula).expect_err("BitVec(32) vs a declared u64");
        assert!(decline.reason().contains("BitVec(32)"), "{decline}");

        let bool_mismatch = Formula::Eq(
            Box::new(Formula::Var("x".to_string(), Sort::Bool)),
            Box::new(Formula::Int(0)),
        );
        assert!(lower(&bool_mismatch).is_err());
    }

    #[test]
    fn a_variable_outside_the_scope_declines() {
        let formula = Formula::Gt(Box::new(var("nope")), Box::new(Formula::Int(0)));
        let decline = lower(&formula).expect_err("free variables are not admitted");
        assert!(decline.reason().contains("nope"), "{decline}");
        assert!(decline.reason().contains("scope"), "{decline}");
    }

    #[test]
    fn connectives_and_implication_lower() {
        let formula = Formula::Implies(
            Box::new(var("b")),
            Box::new(Formula::And(vec![
                Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Not(Box::new(var("b"))),
            ])),
        );
        let lowered = lower(&formula).expect("connectives lower");
        assert!(matches!(lowered, TrustExpr::Implies { .. }));
    }

    /// The SMT-LIB identities for the empty n-ary connectives. Reading `Or([])`
    /// as `true` would prove an empty disjunction.
    #[test]
    fn empty_connectives_use_their_identities() {
        assert_eq!(
            lower(&Formula::And(vec![])).expect("empty conjunction"),
            TrustExpr::bool_literal(true)
        );
        assert_eq!(
            lower(&Formula::Or(vec![])).expect("empty disjunction"),
            TrustExpr::bool_literal(false)
        );
    }

    #[test]
    fn bitvector_operators_carry_their_signedness_onto_the_sort() {
        let unsigned = Formula::BvULt(Box::new(var("x")), Box::new(Formula::Int(7)), 64);
        assert_eq!(
            lower(&unsigned).expect("unsigned compare over a u64"),
            TrustExpr::compare(
                TrustCompareOp::Lt,
                TrustExpr::variable("x", TrustSort::unsigned(64)),
                TrustExpr::int_literal(7, TrustSort::unsigned(64)),
            )
        );

        // A signed compare of an unsigned-declared value changes what is
        // asserted, and trust-vc carries signedness on the sort, so it declines
        // rather than silently becoming the unsigned comparison.
        let signed = Formula::BvSLt(Box::new(var("x")), Box::new(Formula::Int(7)), 64);
        let decline = lower(&signed).expect_err("signed compare of an unsigned value");
        assert!(decline.reason().contains("signed"), "{decline}");

        // A declared width that disagrees with the node's width declines too.
        let wrong_width = Formula::BvULt(Box::new(var("x")), Box::new(Formula::Int(7)), 32);
        assert!(lower(&wrong_width).is_err());
    }

    #[test]
    fn quantifiers_lower_over_int_binders_and_decline_over_bitvector_binders() {
        let body = Formula::Ge(
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let lowered = lower(&Formula::Forall(
            vec![("i".into(), Sort::Int)],
            Box::new(body.clone()),
        ))
        .expect("an Int binder lowers");
        assert!(matches!(lowered, TrustExpr::Quantifier { .. }));

        // Signedness is not on the wire for a binder, and there is no
        // declaration to recover it from.
        let decline = lower(&Formula::Forall(
            vec![("i".into(), Sort::BitVec(64))],
            Box::new(body),
        ))
        .expect_err("a BitVec binder has no recoverable signedness");
        assert!(decline.reason().contains("signedness"), "{decline}");
    }

    /// A Bool-sorted conditional is rewritten losslessly; a value-sorted one has
    /// nothing to rewrite to.
    #[test]
    fn bool_ite_is_rewritten_and_value_ite_declines() {
        let bool_ite = Formula::Ite(
            Box::new(var("b")),
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)))),
            Box::new(Formula::Bool(true)),
        );
        assert!(matches!(
            lower(&bool_ite).expect("bool ite rewrites"),
            TrustExpr::Logic { .. }
        ));

        let value_ite = Formula::Eq(
            Box::new(var("_0")),
            Box::new(Formula::Ite(
                Box::new(var("b")),
                Box::new(var("x")),
                Box::new(Formula::Int(0)),
            )),
        );
        let decline = lower(&value_ite).expect_err("a value-sorted Ite is not expressible");
        assert!(decline.reason().contains("Ite"), "{decline}");
    }

    /// THE FAIL-CLOSED SURFACE of the formula decoder. Every node outside the
    /// scalar fragment declines by name; none is approximated, and in particular
    /// none becomes `true`.
    #[test]
    fn every_unmodelled_node_declines_naming_itself() {
        let x = || Box::new(var("x"));
        let zero = || Box::new(Formula::Int(0));
        let cases: Vec<(Formula, &str)> = vec![
            (Formula::Neg(x()), "Neg"),
            (Formula::Select(x(), zero()), "Select"),
            (Formula::Store(x(), zero(), zero()), "Store"),
            (Formula::Pred("dir_open".into(), vec![var("x")]), "Pred"),
            (
                Formula::FnApp {
                    func: "reference".to_string(),
                    args: vec![var("x")],
                    sort: Sort::Int,
                },
                "FnApp",
            ),
            (
                Formula::Ctor {
                    ctor: "Some".to_string(),
                    args: vec![var("x")],
                    sort: Sort::Int,
                },
                "Ctor",
            ),
            (
                Formula::Sel {
                    datatype: "Option".to_string(),
                    field: "0".to_string(),
                    field_sort: Sort::Int,
                    arg: x(),
                },
                "Sel",
            ),
            (
                Formula::IsCtor {
                    datatype: "Option".to_string(),
                    ctor: "Some".to_string(),
                    arg: x(),
                },
                "IsCtor",
            ),
            (Formula::BvAnd(x(), zero(), 64), "BvAnd"),
            (Formula::BvOr(x(), zero(), 64), "BvOr"),
            (Formula::BvXor(x(), zero(), 64), "BvXor"),
            (Formula::BvNot(x(), 64), "BvNot"),
            (Formula::BvShl(x(), zero(), 64), "BvShl"),
            (Formula::BvLShr(x(), zero(), 64), "BvLShr"),
            (Formula::BvAShr(x(), zero(), 64), "BvAShr"),
            (Formula::BvToInt(x(), 64, false), "BvToInt"),
            (Formula::IntToBv(x(), 64), "IntToBv"),
            (Formula::BvConcat(x(), zero()), "BvConcat"),
            (Formula::BvZeroExt(x(), 64), "BvZeroExt"),
            (Formula::BvSignExt(x(), 64), "BvSignExt"),
            (
                Formula::BvExtract {
                    inner: x(),
                    high: 7,
                    low: 0,
                },
                "BvExtract",
            ),
            (Formula::FpAdd(x(), x(), x()), "FpAdd"),
            (Formula::FpIsNaN(x()), "FpIsNaN"),
            (Formula::FpToIeeeBv(x()), "FpToIeeeBv"),
            (
                Formula::FpConst {
                    bits: 0,
                    eb: 11,
                    sb: 53,
                },
                "FpConst",
            ),
        ];
        for (formula, name) in cases {
            let decline = lower(&formula).expect_err("node is outside the scalar fragment");
            assert!(
                decline.reason().contains(name),
                "decline for {name} must name it, got: {decline}"
            );
            assert!(
                decline.reason().contains("unmodelled") || decline.reason().contains("model"),
                "decline for {name} must read as a refusal, got: {decline}"
            );
        }
    }

    /// A payload the producer failed closed on has NO `formula` key. An absent
    /// predicate is not an empty one.
    #[test]
    fn a_source_only_payload_declines_rather_than_reading_as_vacuous() {
        let source_only = serde_json::json!({
            "source": { "source_id": "rust:probe.rs::inc", "assertion_id": "rust-assertion:1" },
            "predicate_unparseable": "x.foo()",
        })
        .to_string();
        let decline = formula_node("trust-types.Formula@1", &source_only)
            .expect_err("a source-only payload carries no predicate");
        assert!(decline.reason().contains("no `formula` node"), "{decline}");
    }

    /// ROUND-7 MAJOR 1, at the decode seam itself. `predicate_text` — the
    /// grounding the Clean-kernel re-check uses — is
    /// `smtlib.unwrap_or(payload)`, so a row carrying both renderings has the
    /// kernel checking one string and this lane assuming the other, with nothing
    /// upstream binding them.
    #[test]
    fn two_disagreeing_renderings_of_one_formula_decline() {
        let payload = r#"{"formula":{"Ge":[{"Var":["_0","Int"]},{"Int":100}]}}"#;
        let decline = decode_predicate(&trust_ir::ProofFormula {
            schema: "trust-types.Formula@1".to_string(),
            payload: payload.to_string(),
            // The closed tautology trust-ir's own miner will certify.
            smtlib: Some("(>= _0 0)".to_string()),
            sort: Some("Bool".to_string()),
            bindings: Vec::new(),
        })
        .expect_err("the kernel would ground `smtlib` and this lane decodes `payload`");
        assert!(decline.reason().contains("smtlib"), "{decline}");
        assert!(decline.reason().contains("payload"), "{decline}");
    }

    /// The two shapes in which there is only ONE formula: `smtlib` absent, and
    /// `smtlib` byte-identical to `payload` (which is how `ProofFormula::smtlib2`
    /// builds a row). `sort` is never consulted, in either.
    #[test]
    fn one_rendering_decodes_whether_or_not_it_is_spelled_twice() {
        let payload = r#"{"formula":{"Ge":[{"Var":["_0","Int"]},{"Int":0}]}}"#;
        for smtlib in [None, Some(payload.to_string())] {
            decode_predicate(&trust_ir::ProofFormula {
                schema: "trust-types.Formula@1".to_string(),
                payload: payload.to_string(),
                smtlib,
                sort: Some("Bool".to_string()),
                bindings: Vec::new(),
            })
            .expect("one rendering, however many times it is spelled, is one formula");
        }
    }

    #[test]
    fn an_unaccepted_schema_declines_naming_itself() {
        let decline = formula_node("smtlib2", "(>= 5 0)").expect_err("schema is not accepted");
        assert!(decline.reason().contains("smtlib2"), "{decline}");
        assert!(
            decline.reason().contains("trust-types.Formula@1"),
            "{decline}"
        );
        assert_eq!(ACCEPTED_FORMULA_SCHEMAS, &["trust-types.Formula@1"]);
    }

    /// A predicate that is not `Bool` at the root is not a proof obligation.
    #[test]
    fn a_non_bool_root_declines() {
        let decline = lower(&var("x")).expect_err("a u64 is not a predicate");
        assert!(decline.reason().contains("expected"), "{decline}");
    }

    #[test]
    fn canonical_ingress_refuses_duplicate_fields_and_malformed_operands() {
        for payload in [
            r#"{"formula":{"Bool":false},"formula":{"Bool":true}}"#,
            r#"{"formula":{"Bool":false,"Bool":true}}"#,
            r#"{"formula":{"BitVec":{"value":0,"value":1,"width":8}}}"#,
            r#"{"formula":{"Var":["x","Int",true]}}"#,
            r#"{"formula":{"Eq":[{"Bool":true},{"Bool":true},{"Bool":false}]}}"#,
            r#"{"formula":{"Var":["x",{"BitVec":-1}]}}"#,
            r#"{"formula":{"FuturePredicate":true}}"#,
        ] {
            assert!(
                formula_node(ACCEPTED_FORMULA_SCHEMAS[0], payload).is_err(),
                "{payload}"
            );
        }
    }

    #[test]
    fn canonical_ingress_keeps_exact_wide_integer_values() {
        for value in [i128::MIN, i128::MAX, i128::from(u64::MAX)] {
            let formula = Formula::Int(value);
            assert_eq!(
                formula_node(ACCEPTED_FORMULA_SCHEMAS[0], &payload(&formula)).unwrap(),
                formula
            );
        }
        let formula = Formula::UInt(u128::MAX);
        assert_eq!(
            formula_node(ACCEPTED_FORMULA_SCHEMAS[0], &payload(&formula)).unwrap(),
            formula
        );
        let scope: Scope = [("m".into(), ScopeEntry::new("m".into(), TrustSort::MathInt))].into();
        for value in [i128::MIN, i128::MAX] {
            let formula = Formula::Eq(
                Box::new(Formula::Var("m".into(), Sort::Int)),
                Box::new(Formula::Int(value)),
            );
            let node = formula_node(ACCEPTED_FORMULA_SCHEMAS[0], &payload(&formula)).unwrap();
            assert_eq!(
                FormulaDecoder::new(&scope).lower_predicate(&node).unwrap(),
                TrustExpr::compare(
                    TrustCompareOp::Eq,
                    TrustExpr::variable("m", TrustSort::MathInt),
                    TrustExpr::int_literal(value, TrustSort::MathInt)
                )
            );
        }
        assert!(FormulaDecoder::new(&scope)
            .lower_predicate(&Formula::Eq(
                Box::new(Formula::Var("m".into(), Sort::Int)),
                Box::new(Formula::UInt(u128::MAX))
            ))
            .is_err());
    }

    #[test]
    fn canonical_question_changes_remain_distinct_and_scope_checked() {
        let original = Formula::Ge(Box::new(var("x")), Box::new(Formula::Int(0)));
        let changed = Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(0)));
        assert_ne!(
            lower(&original).unwrap(),
            lower(&changed).unwrap(),
            "a changed original claim must not reuse its old reading"
        );
        let quantified = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Ge(
                Box::new(Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)))),
                Box::new(var("x")),
            )),
        );
        let scoped = scope();
        let mut decoder = FormulaDecoder::new(&scoped);
        let node = formula_node(ACCEPTED_FORMULA_SCHEMAS[0], &payload(&quantified)).unwrap();
        let lowered = decoder.lower_predicate(&node).unwrap();
        assert!(matches!(lowered, TrustExpr::Quantifier { .. }));
        assert_eq!(
            decoder.declared("x").unwrap().sort,
            TrustSort::unsigned(64),
            "the binder must not escape"
        );
        let free = Formula::Ge(
            Box::new(Formula::SymVar("not_declared".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        assert!(lower(&free).unwrap_err().reason().contains("not_declared"));
    }

    #[test]
    fn canonical_ingress_retains_the_original_json_depth_bound() {
        let nested = |depth: usize| {
            format!(
                "{{\"formula\":{}{{\"Bool\":true}}{}}}",
                "{\"Not\":".repeat(depth),
                "}".repeat(depth)
            )
        };
        let near = nested(40);
        assert!(serde_json::from_str::<Value>(&near).is_ok());
        assert!(formula_node(ACCEPTED_FORMULA_SCHEMAS[0], &near).is_ok());
        let deep = nested(160);
        assert!(serde_json::from_str::<Value>(&deep).is_err());
        assert!(formula_node(ACCEPTED_FORMULA_SCHEMAS[0], &deep).is_err());
        let metadata = format!(
            "{{\"formula\":{{\"Bool\":true}},\"source\":{}0{}}}",
            "[".repeat(160),
            "]".repeat(160)
        );
        assert!(serde_json::from_str::<Value>(&metadata).is_err());
        assert!(formula_node(ACCEPTED_FORMULA_SCHEMAS[0], &metadata).is_err());
    }

    #[test]
    fn native_formula_boundary_uses_only_the_canonical_wire_type() {
        let _: fn(&trust_ir::ProofFormula) -> Result<Formula, Decline> = decode_predicate;
        let source = include_str!("formula.rs")
            .split_once("#[cfg(test)]")
            .unwrap()
            .0;
        for forbidden in [
            "fn tagged(",
            "fn pair(",
            "fn wide_int(",
            "fn wide_uint(",
            "enum WireSort",
            "from_value",
        ] {
            assert!(
                !source.contains(forbidden),
                "copied or pre-decoded question ingress returned: {forbidden}"
            );
        }
        let manifest = include_str!("../../Cargo.toml")
            .split_once("[dev-dependencies]")
            .unwrap()
            .0;
        assert!(
            manifest.contains("trust-ir-contract = { workspace = true }"),
            "the canonical codec must be linked in production"
        );
    }

    fn verify_canonical_question(formula: &Formula) -> crate::TrustOutcome {
        let lowered = lower(formula).expect("the original canonical question lowers exactly");
        let unit = crate::TrustTypedProofUnit::new("canonical-formula", "canonical::arithmetic")
            .with_obligation(crate::TypedProofObligation::assert(
                "original",
                lowered.to_trust_vc_expr().unwrap(),
            ));
        crate::TrustVcTrustEngine::new()
            .verify_typed_proof_unit(&unit)
            .unwrap()
            .units()[0]
            .outcome()
            .clone()
    }

    fn math_question(body: Formula) -> Formula {
        Formula::Forall(vec![("n".into(), Sort::Int)], Box::new(body))
    }

    fn n() -> Box<Formula> {
        Box::new(Formula::Var("n".into(), Sort::Int))
    }

    #[test]
    fn canonical_negative_integer_predicates_cannot_be_verified_as_euclidean() {
        // Canonical n=-1 yields -1, not the nonnegative Euclidean remainder.
        let rem = math_question(Formula::Ge(
            Box::new(Formula::Rem(n(), Box::new(Formula::Int(5)))),
            Box::new(Formula::Int(0)),
        ));
        let div = math_question(Formula::Implies(
            Box::new(Formula::Lt(n(), Box::new(Formula::Int(0)))),
            Box::new(Formula::Lt(
                Box::new(Formula::Div(n(), Box::new(Formula::Int(2)))),
                Box::new(Formula::Int(0)),
            )),
        ));
        for formula in [rem, div] {
            let outcome = verify_canonical_question(&formula);
            assert_ne!(outcome, crate::TrustOutcome::Verified, "a negative-valued counterexample to the WHOLE original predicate was lost: {formula:?}");
        }
    }

    #[test]
    fn canonical_truncated_values_are_exact_for_both_operand_signs() {
        for a in [-7i128, -1, 0, 1, 7] {
            for b in [-5i128, -2, 2, 5] {
                for (is_div, expected) in [(false, a % b), (true, a / b)] {
                    let dividend = Box::new(Formula::Add(n(), Box::new(Formula::Int(a))));
                    let operation = if is_div {
                        Formula::Div(dividend, Box::new(Formula::Int(b)))
                    } else {
                        Formula::Rem(dividend, Box::new(Formula::Int(b)))
                    };
                    // n=0 is part of this original question, never an adapter premise.
                    let formula = math_question(Formula::Implies(
                        Box::new(Formula::Eq(n(), Box::new(Formula::Int(0)))),
                        Box::new(Formula::Eq(
                            Box::new(operation),
                            Box::new(Formula::Int(expected)),
                        )),
                    ));
                    assert_eq!(
                        verify_canonical_question(&formula),
                        crate::TrustOutcome::Verified,
                        "canonical {}({a}, {b}) must equal {expected}",
                        if is_div { "Div" } else { "Rem" }
                    );
                }
            }
        }
    }

    #[test]
    fn truncated_math_refuses_zero_and_expansion_exhaustion() {
        for operation in [
            Formula::Rem(n(), Box::new(Formula::Int(0))),
            Formula::Div(n(), Box::new(Formula::Int(0))),
        ] {
            let formula =
                math_question(Formula::Eq(Box::new(operation), Box::new(Formula::Int(0))));
            assert!(lower(&formula).unwrap_err().reason().contains("zero"));
        }
        let mut nested = *n();
        for _ in 0..20 {
            nested = Formula::Rem(Box::new(nested), Box::new(Formula::Int(5)));
        }
        let formula = math_question(Formula::Eq(Box::new(nested), Box::new(Formula::Int(0))));
        assert!(
            lower(&formula).unwrap_err().reason().contains("4096"),
            "resource exhaustion is a refusal, never a premise"
        );
    }

    #[test]
    fn verus_math_remainder_keeps_its_euclidean_semantics() {
        let x = TrustExpr::variable("x", TrustSort::MathInt);
        let expr = TrustExpr::compare(
            TrustCompareOp::Ge,
            TrustExpr::arith(
                crate::TrustArithOp::Rem,
                x,
                TrustExpr::int_literal(5, TrustSort::MathInt),
                TrustSort::MathInt,
            ),
            TrustExpr::int_literal(0, TrustSort::MathInt),
        );
        let unit = crate::TrustTypedProofUnit::new("verus-math", "verus::remainder")
            .with_variable(crate::TrustVariable::new("x", TrustSort::MathInt))
            .with_obligation(crate::TypedProofObligation::assert(
                "euclidean",
                expr.to_trust_vc_expr().unwrap(),
            ));
        let report = crate::TrustVcTrustEngine::new()
            .verify_typed_proof_unit(&unit)
            .unwrap();
        assert_eq!(report.units()[0].outcome(), &crate::TrustOutcome::Verified);
    }
}
