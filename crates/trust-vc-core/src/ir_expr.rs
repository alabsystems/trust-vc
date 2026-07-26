//! Typed expression IR for trust_vc verification conditions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `TrustVcExpr` is a closed enum representing all expression forms between
//! `syn::Expr` (input) and `ay Term` (output). Unsupported `syn::Expr`
//! variants produce `LoweringError` during lowering — no silent drops.
//!
//! Part of #1550 Phase 3 (#1864).

use crate::ir::{DatatypeVariant, TrustVcType};
use crate::ir_place::TrustVcPlace;

/// Arithmetic operators for integer/bitvector expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

/// Comparison operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CompareOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Logical operators (short-circuit boolean).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LogicOp {
    And,
    Or,
}

/// Bitwise and shift operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SpecialArithOp {
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

/// Quantifier kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum QuantifierKind {
    Forall,
    Exists,
}

/// Collection operation identifiers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CollectionOp {
    // Seq operations
    Len,
    IsEmpty,
    Push,
    Add,
    First,
    Last,
    Update,
    DropLast,
    DropFirst,
    Take,
    Skip,
    Subrange,
    Concat,
    View,
    SeqMapValues,
    SeqMap,
    SeqFilter,
    SeqFlatMap,
    SeqFoldLeft,
    SeqFoldRight,
    Reverse,
    NoDuplicates,
    ToSet,
    ToMultiset,
    // Set operations
    Contains,
    Insert,
    Remove,
    Union,
    Intersect,
    Difference,
    Subset,
    Superset,
    Finite,
    SetFilter,
    SetMap,
    SetMkMap,
    SetFold,
    // Multiset operations
    Count,
    Choose,
    // Map operations
    Get,
    ContainsKey,
    ContainsValue,
    Dom,
    MapMapValues,
    MapMapEntries,
    MapFilterKeys,
}

pub(crate) const TUPLE_VARIANT_NAME: &str = "Tuple";

pub(crate) fn tuple_datatype_type(element_tys: Vec<TrustVcType>) -> TrustVcType {
    let name = tuple_datatype_name(&element_tys);
    let fields = element_tys
        .into_iter()
        .enumerate()
        .map(|(index, ty)| (index.to_string(), ty))
        .collect();
    TrustVcType::Datatype {
        name,
        variants: vec![DatatypeVariant::new(TUPLE_VARIANT_NAME, fields)],
    }
}

pub(crate) fn tuple_datatype_name(element_tys: &[TrustVcType]) -> String {
    match element_tys {
        [] => "()".to_string(),
        [ty] => format!("({},)", ty.to_type_string()),
        _ => format!(
            "({})",
            element_tys
                .iter()
                .map(TrustVcType::to_type_string)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

#[cfg(feature = "native-strings")]
pub(crate) const NATIVE_STRING_STARTS_WITH_FN: &str = "__trust_vc_native_string_starts_with";
#[cfg(feature = "native-strings")]
pub(crate) const NATIVE_STRING_ENDS_WITH_FN: &str = "__trust_vc_native_string_ends_with";

/// Integer constant kinds (associated constants like i32::MAX).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum IntConstKind {
    Min,
    Max,
}

/// A single named field in a struct pattern like `Point { x, y: z, .. }`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct StructPatternField {
    /// The field name in the struct definition.
    pub field_name: String,
    /// The binding name, or `None` for wildcard (`_`).
    pub binding: Option<String>,
}

impl StructPatternField {
    #[must_use]
    pub fn new(field_name: impl Into<String>, binding: Option<String>) -> Self {
        Self {
            field_name: field_name.into(),
            binding,
        }
    }
}

/// A pattern in a match arm.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
#[allow(clippy::large_enum_variant)]
pub enum MatchPattern {
    /// Literal value (integer or bool).
    Lit(TrustVcExpr),
    /// Named binding.
    Ident(String),
    /// Datatype constructor pattern such as `Some(x)` or `None`.
    ///
    /// `has_rest` mirrors [`MatchPattern::Struct::has_rest`]: when `true`, a
    /// trailing `..` rest was present (e.g. `MatchQuad(first, ..)` or the tuple
    /// pattern `(f, ..)`), so only the LEADING `bindings` are bound to the
    /// first N field selectors and the remaining fields are ignored. When
    /// `false`, the pattern is exact-arity (`bindings.len() == variant.fields`).
    /// Only a TRAILING rest is representable here — a binding after `..` (a
    /// middle/back rest) needs a field-index remap and is rejected at lowering.
    Constructor {
        variant_name: String,
        bindings: Vec<String>,
        has_rest: bool,
    },
    /// Named-field struct/variant pattern such as `Point { x, y: _ }`.
    Struct {
        variant_name: String,
        fields: Vec<StructPatternField>,
        has_rest: bool,
    },
    /// Wildcard `_`.
    Wildcard,
    /// Or-pattern `A | B`.
    Or(Vec<MatchPattern>),
}

/// A single arm in a match expression.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct MatchArm {
    pub pattern: MatchPattern,
    pub body: TrustVcExpr,
    /// Optional match guard (`P if g => ...`). A pure boolean spec expression that
    /// references the arm's pattern bindings; the arm is taken only when the pattern
    /// matches AND the guard holds. `None` = no guard (the arm is taken whenever its
    /// pattern matches). A guarded arm is NOT exhaustive over its pattern (the guard
    /// may be false), so it can never seed an exhaustiveness default or a
    /// ground-constructor reduction.
    pub guard: Option<TrustVcExpr>,
}

impl MatchArm {
    /// Creates a guardless match arm from a pattern and body expression. Guarded
    /// arms are constructed with the `guard` field directly (same-crate literal).
    #[must_use]
    pub fn new(pattern: MatchPattern, body: TrustVcExpr) -> Self {
        Self {
            pattern,
            body,
            guard: None,
        }
    }
}

/// Wrapping mode for arithmetic methods.
///
/// These map to Rust's `wrapping_*`, `checked_*`, and `saturating_*` method
/// families, but the encoding semantics differ from Rust's runtime semantics
/// where noted (see [`WrappingMode::Checked`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum WrappingMode {
    /// `wrapping_add`, `wrapping_sub`, etc. — BV modular arithmetic, no overflow checks.
    Wrapping,
    /// `checked_add`, `checked_sub`, etc. — overflow-checked arithmetic.
    ///
    /// **Semantics gap**: In Rust, `checked_*` returns `Option<T>` (`Some` on
    /// success, `None` on overflow). This encoding does NOT model `Option<T>`.
    /// Instead, it computes the BV result (same as `wrapping_*`) and pushes
    /// overflow/underflow predicates to the encoder's `overflow_checks` side
    /// channel. Verification fails if overflow is possible (refutation check).
    ///
    /// This is the standard verification-tool encoding: "perform the operation
    /// and prove no overflow occurs." It is correct for proving absence of
    /// overflow but cannot model code that branches on `Some`/`None`.
    ///
    /// `Option<T>` encoding requires ADT support (not yet implemented).
    Checked,
    /// `saturating_add`, `saturating_sub`, etc. — clamp result to type bounds.
    Saturating,
}

/// Typed expression IR for trust_vc verification conditions.
///
/// Closed enum for all expression forms that trust_vc can encode to ay.
/// Sits between `syn::Expr` and `ay Term`. Unsupported variants produce
/// `LoweringError` during lowering — no silent drops.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TrustVcExpr {
    /// Unit literal: `()`.
    UnitLit,
    /// Boolean literal: `true` or `false`.
    BoolLit(bool),
    /// Native string literal.
    StringLit(String),
    /// Integer literal with known type.
    IntLit { value: i128, ty: TrustVcType },
    /// Variable reference, resolved to a type.
    Var { name: String, ty: TrustVcType },
    /// Standard arithmetic: `+`, `-`, `*`, `/`, `%`.
    Arith {
        op: ArithOp,
        left: Box<Self>,
        right: Box<Self>,
        ty: TrustVcType,
    },
    /// Arithmetic negation: `-x`.
    Neg(Box<Self>),
    /// Comparison: `==`, `!=`, `<`, `<=`, `>`, `>=`.
    Compare {
        op: CompareOp,
        left: Box<Self>,
        right: Box<Self>,
    },
    /// Short-circuit logical: `&&`, `||`.
    Logic {
        op: LogicOp,
        left: Box<Self>,
        right: Box<Self>,
    },
    /// Logical negation: `!x`.
    Not(Box<Self>),
    /// Logical implication: `premise ==> conclusion`.
    Implies {
        premise: Box<Self>,
        conclusion: Box<Self>,
    },
    /// Conditional: `if cond { then } else { otherwise }`.
    Ite {
        cond: Box<Self>,
        then_branch: Box<Self>,
        else_branch: Box<Self>,
        ty: TrustVcType,
    },
    /// Pattern match, encoded as chained ite.
    Match {
        scrutinee: Box<Self>,
        arms: Vec<MatchArm>,
        ty: TrustVcType,
    },
    /// Let binding: `let name: ty = value; body`.
    Let {
        name: String,
        ty: TrustVcType,
        value: Box<Self>,
        body: Box<Self>,
    },
    /// Type cast: `expr as to_ty`.
    Cast {
        expr: Box<Self>,
        from_ty: TrustVcType,
        to_ty: TrustVcType,
    },
    /// Collection method call (Seq/Set/Map operations).
    CollectionOp {
        op: CollectionOp,
        receiver: Box<Self>,
        receiver_name: Option<String>,
        args: Vec<Self>,
        ty: TrustVcType,
    },
    /// Array/Seq indexing: `receiver[index]`.
    Index {
        receiver: Box<Self>,
        index: Box<Self>,
        receiver_name: Option<String>,
        elem_ty: TrustVcType,
    },
    /// Universal or existential quantifier.
    Quantifier {
        kind: QuantifierKind,
        bound_vars: Vec<(String, TrustVcType)>,
        body: Box<Self>,
        triggers: Option<Vec<Vec<Self>>>,
        /// Trigger inference mode captured from `#[auto_trigger]` /
        /// `#[all_triggers]` at quantifier construction time. `None` means
        /// use the default (Conservative). Part of #2461.
        trigger_inference_mode: Option<crate::trigger_inference::TriggerInferenceMode>,
    },
    /// Named function call (uninterpreted or proof function).
    FnCall {
        name: String,
        args: Vec<Self>,
        return_ty: TrustVcType,
    },
    /// Spec-only closure literal produced by `SpecFn::new(|...| ...)`.
    SpecClosure {
        params: Vec<(String, TrustVcType)>,
        body: Box<Self>,
        ty: TrustVcType,
    },
    /// Integer associated constant: `T::MIN`, `T::MAX`.
    IntConst { ty: TrustVcType, kind: IntConstKind },
    /// Bitwise and shift operations.
    SpecialArith {
        op: SpecialArithOp,
        left: Box<Self>,
        right: Box<Self>,
        ty: TrustVcType,
    },
    /// Wrapping/checked/saturating arithmetic method call.
    ///
    /// For `Checked` mode: returns the raw BV result (not `Option<T>`) and
    /// emits overflow predicates via the encoder's side channel. See
    /// [`WrappingMode::Checked`] for the semantics gap with Rust's API.
    WrappingArith {
        mode: WrappingMode,
        op: ArithOp,
        left: Box<Self>,
        right: Box<Self>,
        ty: TrustVcType,
    },
    /// Hilbert choice (witness extraction from existential quantifier).
    ///
    /// `choose!(|x: T| cond(x))` returns some `x: T` satisfying `cond(x)` if one
    /// exists, otherwise an arbitrary value. Encoded via Skolem function + axiom.
    /// Part of #2143.
    Choose {
        var_name: String,
        var_ty: TrustVcType,
        condition: Box<Self>,
        key: String,
        /// Optional extra axiom asserted (as a hypothesis) when this choose is
        /// first encoded, in addition to the standard Skolem-witness axiom.
        ///
        /// Used by the multi-binder `choose|i, j| P(i, j)` lowering: the per-field
        /// decomposition reliably handles direct/arithmetic predicates (via its
        /// inner-`exists` Skolemization), but its nested-`exists` trigger cannot
        /// instantiate for an OPAQUE / spec-fn `P`. Attaching the derivable
        /// combined axiom `forall i, j. P(i, j) ==> P(chosen_i, chosen_j)` (whose
        /// scalar `P(i, j)` trigger matches a surrounding `exists i, j. P(i, j)`
        /// Skolem) to the last per-field choose closes that gap. Sound because the
        /// combined axiom is a theorem of the per-field Skolem axioms.
        also_assert: Option<Box<Self>>,
    },
    /// Read the current value at a memory place.
    ///
    /// Lets the encoder resolve a place (root + projections) to a value
    /// without flattening to a synthetic shadow-variable name too early.
    /// Part of #2515.
    ReadPlace {
        place: TrustVcPlace,
        ty: TrustVcType,
    },
    /// Boolean: are two memory places disjoint (non-aliasing)?
    ///
    /// Encoded to a Boolean SMT term based on the disjointness rules
    /// (different roots, different fields, different indices).
    /// Part of #2515.
    PlaceDisjoint {
        left: TrustVcPlace,
        right: TrustVcPlace,
    },
    /// Create a fresh prophecy variable (unconstrained symbolic constant).
    /// Part of #2519.
    ProphecyNew { name: String, ty: TrustVcType },
    /// Resolve a prophecy: constrain it to equal the given value.
    /// Part of #2519.
    ProphecyResolve { name: String, value: Box<Self> },
}

impl std::fmt::Display for ArithOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ArithOp::Add => write!(f, "+"),
            ArithOp::Sub => write!(f, "-"),
            ArithOp::Mul => write!(f, "*"),
            ArithOp::Div => write!(f, "/"),
            ArithOp::Rem => write!(f, "%"),
        }
    }
}

impl std::fmt::Display for CompareOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompareOp::Eq => write!(f, "=="),
            CompareOp::Ne => write!(f, "!="),
            CompareOp::Lt => write!(f, "<"),
            CompareOp::Le => write!(f, "<="),
            CompareOp::Gt => write!(f, ">"),
            CompareOp::Ge => write!(f, ">="),
        }
    }
}

impl std::fmt::Display for LogicOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LogicOp::And => write!(f, "&&"),
            LogicOp::Or => write!(f, "||"),
        }
    }
}

impl std::fmt::Display for SpecialArithOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpecialArithOp::BitAnd => write!(f, "&"),
            SpecialArithOp::BitOr => write!(f, "|"),
            SpecialArithOp::BitXor => write!(f, "^"),
            SpecialArithOp::Shl => write!(f, "<<"),
            SpecialArithOp::Shr => write!(f, ">>"),
        }
    }
}

#[cfg(test)]
#[path = "ir_expr_arbitrary.rs"]
pub(crate) mod arbitrary;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::TrustVcType;

    // --- Helper constructors ---

    fn i32_ty() -> TrustVcType {
        TrustVcType::Int { width: 32 }
    }

    fn u64_ty() -> TrustVcType {
        TrustVcType::Uint { width: 64 }
    }

    fn i32_var(name: &str) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty: i32_ty(),
        }
    }

    fn i32_lit(value: i128) -> TrustVcExpr {
        TrustVcExpr::IntLit {
            value,
            ty: i32_ty(),
        }
    }

    // --- Display impls ---

    #[test]
    fn test_arith_op_display_all_variants() {
        assert_eq!(format!("{}", ArithOp::Add), "+");
        assert_eq!(format!("{}", ArithOp::Sub), "-");
        assert_eq!(format!("{}", ArithOp::Mul), "*");
        assert_eq!(format!("{}", ArithOp::Div), "/");
        assert_eq!(format!("{}", ArithOp::Rem), "%");
    }

    #[test]
    fn test_compare_op_display_all_variants() {
        assert_eq!(format!("{}", CompareOp::Eq), "==");
        assert_eq!(format!("{}", CompareOp::Ne), "!=");
        assert_eq!(format!("{}", CompareOp::Lt), "<");
        assert_eq!(format!("{}", CompareOp::Le), "<=");
        assert_eq!(format!("{}", CompareOp::Gt), ">");
        assert_eq!(format!("{}", CompareOp::Ge), ">=");
    }

    #[test]
    fn test_logic_op_display_all_variants() {
        assert_eq!(format!("{}", LogicOp::And), "&&");
        assert_eq!(format!("{}", LogicOp::Or), "||");
    }

    #[test]
    fn test_special_arith_op_display_all_variants() {
        assert_eq!(format!("{}", SpecialArithOp::BitAnd), "&");
        assert_eq!(format!("{}", SpecialArithOp::BitOr), "|");
        assert_eq!(format!("{}", SpecialArithOp::BitXor), "^");
        assert_eq!(format!("{}", SpecialArithOp::Shl), "<<");
        assert_eq!(format!("{}", SpecialArithOp::Shr), ">>");
    }

    // --- StructPatternField ---

    #[test]
    fn test_struct_pattern_field_new_with_binding() {
        let field = StructPatternField::new("x", Some("my_x".to_string()));
        assert_eq!(field.field_name, "x");
        assert_eq!(field.binding, Some("my_x".to_string()));
    }

    #[test]
    fn test_struct_pattern_field_new_wildcard_binding() {
        let field = StructPatternField::new("y", None);
        assert_eq!(field.field_name, "y");
        assert_eq!(field.binding, None);
    }

    #[test]
    fn test_struct_pattern_field_equality() {
        let a = StructPatternField::new("x", Some("a".to_string()));
        let b = StructPatternField::new("x", Some("a".to_string()));
        let c = StructPatternField::new("x", Some("b".to_string()));
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    // --- MatchArm ---

    #[test]
    fn test_match_arm_new_preserves_pattern_and_body() {
        let pattern = MatchPattern::Wildcard;
        let body = TrustVcExpr::BoolLit(true);
        let arm = MatchArm::new(pattern.clone(), body.clone());
        assert_eq!(arm.pattern, pattern);
        assert_eq!(arm.body, body);
    }

    // --- TrustVcExpr structural equality ---

    #[test]
    fn test_trust_vc_expr_arith_structural_equality() {
        let expr1 = TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(i32_var("x")),
            right: Box::new(i32_lit(1)),
            ty: i32_ty(),
        };
        let expr2 = TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(i32_var("x")),
            right: Box::new(i32_lit(1)),
            ty: i32_ty(),
        };
        let expr3 = TrustVcExpr::Arith {
            op: ArithOp::Sub,
            left: Box::new(i32_var("x")),
            right: Box::new(i32_lit(1)),
            ty: i32_ty(),
        };
        assert_eq!(expr1, expr2);
        assert_ne!(
            expr1, expr3,
            "different ArithOp should produce different exprs"
        );
    }

    #[test]
    fn test_trust_vc_expr_nested_logic_equality() {
        // (x > 0) && (y < 10) should equal itself structurally
        let inner_left = TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(i32_var("x")),
            right: Box::new(i32_lit(0)),
        };
        let inner_right = TrustVcExpr::Compare {
            op: CompareOp::Lt,
            left: Box::new(i32_var("y")),
            right: Box::new(i32_lit(10)),
        };
        let logic1 = TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(inner_left.clone()),
            right: Box::new(inner_right.clone()),
        };
        let logic2 = TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(inner_left),
            right: Box::new(inner_right),
        };
        assert_eq!(logic1, logic2);
    }

    // --- TrustVcExpr variant construction and Debug ---

    #[test]
    fn test_trust_vc_expr_ite_construction() {
        let ite = TrustVcExpr::Ite {
            cond: Box::new(TrustVcExpr::BoolLit(true)),
            then_branch: Box::new(i32_lit(1)),
            else_branch: Box::new(i32_lit(0)),
            ty: i32_ty(),
        };
        // Verify Debug doesn't panic and the structure is correct
        let debug = format!("{:?}", ite);
        assert!(
            debug.contains("Ite"),
            "Debug output should contain variant name"
        );
        // Verify equality distinguishes branches
        let ite_swapped = TrustVcExpr::Ite {
            cond: Box::new(TrustVcExpr::BoolLit(true)),
            then_branch: Box::new(i32_lit(0)),
            else_branch: Box::new(i32_lit(1)),
            ty: i32_ty(),
        };
        assert_ne!(ite, ite_swapped, "swapped branches should be distinct");
    }

    #[test]
    fn test_trust_vc_expr_let_binding_body_determines_equality() {
        let let1 = TrustVcExpr::Let {
            name: "tmp".to_string(),
            ty: i32_ty(),
            value: Box::new(i32_lit(42)),
            body: Box::new(i32_var("tmp")),
        };
        let let2 = TrustVcExpr::Let {
            name: "tmp".to_string(),
            ty: i32_ty(),
            value: Box::new(i32_lit(42)),
            body: Box::new(i32_lit(99)),
        };
        assert_ne!(let1, let2, "different body should make lets unequal");
    }

    #[test]
    fn test_trust_vc_expr_cast_from_to_types_matter() {
        let cast1 = TrustVcExpr::Cast {
            expr: Box::new(i32_var("x")),
            from_ty: i32_ty(),
            to_ty: u64_ty(),
        };
        let cast2 = TrustVcExpr::Cast {
            expr: Box::new(i32_var("x")),
            from_ty: i32_ty(),
            to_ty: i32_ty(),
        };
        assert_ne!(
            cast1, cast2,
            "different to_ty should produce different casts"
        );
    }

    // --- MatchPattern variants ---

    #[test]
    fn test_match_pattern_or_contains_multiple_patterns() {
        let or_pattern = MatchPattern::Or(vec![
            MatchPattern::Lit(i32_lit(1)),
            MatchPattern::Lit(i32_lit(2)),
            MatchPattern::Wildcard,
        ]);
        match &or_pattern {
            MatchPattern::Or(pats) => assert_eq!(pats.len(), 3),
            other => panic!("expected Or pattern, got: {:?}", other),
        }
    }

    #[test]
    fn test_match_pattern_constructor_with_bindings() {
        let some_pattern = MatchPattern::Constructor {
            variant_name: "Some".to_string(),
            bindings: vec!["inner".to_string()],
            has_rest: false,
        };
        let none_pattern = MatchPattern::Constructor {
            variant_name: "None".to_string(),
            bindings: vec![],
            has_rest: false,
        };
        assert_ne!(some_pattern, none_pattern);
        if let MatchPattern::Constructor { bindings, .. } = &some_pattern {
            assert_eq!(bindings.len(), 1);
        }
        if let MatchPattern::Constructor { bindings, .. } = &none_pattern {
            assert!(bindings.is_empty());
        }
    }

    #[test]
    fn test_match_pattern_struct_with_rest() {
        let pat = MatchPattern::Struct {
            variant_name: "Point".to_string(),
            fields: vec![StructPatternField::new("x", Some("px".to_string()))],
            has_rest: true,
        };
        match &pat {
            MatchPattern::Struct {
                fields, has_rest, ..
            } => {
                assert_eq!(fields.len(), 1);
                assert!(
                    has_rest,
                    "has_rest should be true for Point with rest pattern"
                );
            }
            other => panic!("expected Struct pattern, got: {:?}", other),
        }
    }

    // --- Clone independence ---

    #[test]
    fn test_trust_vc_expr_clone_produces_independent_copy() {
        let original = TrustVcExpr::Implies {
            premise: Box::new(TrustVcExpr::BoolLit(true)),
            conclusion: Box::new(TrustVcExpr::Compare {
                op: CompareOp::Ge,
                left: Box::new(i32_var("x")),
                right: Box::new(i32_lit(0)),
            }),
        };
        let cloned = original.clone();
        assert_eq!(original, cloned);
        // Verify they are structurally equal but the clone is a separate allocation
        // by checking Debug output matches (no shared-mutation possible)
        assert_eq!(format!("{:?}", original), format!("{:?}", cloned));
    }
}
