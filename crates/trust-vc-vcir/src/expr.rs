//! Expressions and places.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! One expression type serves spec code and exec code. Expressions have no
//! side effects and never call exec or proof functions: a producer flattens
//! calls, assignments and short-circuit operators with effects into
//! statements. What differs between modes is the arithmetic, and that is
//! explicit on each node:
//!
//! * An operation with `check: Some(site)` is exec arithmetic on a machine
//!   type. Its operands and result have that type, the result is the exact
//!   mathematical value, and `site` is where the VC generator checks that
//!   this value exists (no overflow, no division by zero, shift amount in
//!   range). Such nodes appear only in exec code outside ghost blocks.
//! * An operation with `check: None` is spec arithmetic. `+ - * -x` have type
//!   `int` (or `nat` for `+` and `*` of `nat` operands) and compute the exact
//!   value, as Verus spec arithmetic does; a producer converts machine-typed
//!   operands with [`CastKind::Exact`] first. `/` and `%` on `int`/`nat` are
//!   Euclidean.
//!
//! Operands of `&&`, `||`, `==>` and `if` are pure, but a checked operation
//! in a branch that is not taken must not be reported: the VC generator
//! checks such a site under the condition that reaches it.

use crate::ids::{AdtId, FnId, LocalId, SiteId, SpanId};
use crate::ty::Ty;

/// An integer literal: sign and magnitude, so every Rust literal from
/// `i128::MIN` to `u128::MAX` is exact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IntLit {
    /// True for a value below zero. Zero is never negative.
    pub negative: bool,
    /// Absolute value.
    pub magnitude: u128,
}

impl IntLit {
    /// The literal for `value`.
    #[must_use]
    pub const fn from_i128(value: i128) -> Self {
        Self {
            negative: value < 0,
            magnitude: value.unsigned_abs(),
        }
    }

    /// The value as `i128`, when it fits.
    #[must_use]
    pub fn to_i128(self) -> Option<i128> {
        match (self.negative, i128::try_from(self.magnitude)) {
            (false, Ok(magnitude)) => Some(magnitude),
            // `magnitude` is non-negative here, so the negation cannot overflow.
            (true, Ok(magnitude)) => magnitude.checked_neg(),
            // 2^127 is the one negative magnitude that does not fit `i128`
            // but whose negation does.
            (true, Err(_)) => (self.magnitude == 1u128 << 127).then_some(i128::MIN),
            (false, Err(_)) => None,
        }
    }
}

/// A literal value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Lit {
    /// `true` or `false`.
    Bool(bool),
    /// An integer of the expression's integer type.
    Int(IntLit),
    /// `()`.
    Unit,
}

/// One step from a place to a sub-place.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Projection {
    /// Through a reference.
    Deref,
    /// A field of a struct (variant 0) or of an enum variant.
    Field {
        /// Variant index; 0 for a struct.
        variant: u32,
        /// Field index within the variant.
        field: u32,
    },
    /// An element of a tuple.
    TupleField(u32),
}

/// A memory location: a local followed by projections.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Place {
    /// The root local.
    pub local: LocalId,
    /// Projections applied in order.
    pub projections: Vec<Projection>,
}

impl Place {
    /// The place that is just `local`.
    #[must_use]
    pub const fn local(local: LocalId) -> Self {
        Self {
            local,
            projections: Vec::new(),
        }
    }

    /// `*local`.
    #[must_use]
    pub fn deref(local: LocalId) -> Self {
        Self {
            local,
            projections: vec![Projection::Deref],
        }
    }

    /// Does the place go through a reference?
    #[must_use]
    pub fn has_deref(&self) -> bool {
        self.projections.contains(&Projection::Deref)
    }
}

/// Unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    /// `!` on `bool`, or bitwise not on a machine integer.
    Not,
    /// Arithmetic negation.
    Neg,
}

/// Exact primitive constants, interpreted in a complete architecture context.
/// Native producers recognize their actual primitive inherent owner; a user
/// function or associated constant with the same name has no such meaning.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntegerConstant {
    WordBits,
    Minimum(crate::IntRange),
    Maximum(crate::IntRange),
    Bits(crate::IntRange),
}

impl IntegerConstant {
    pub fn value(self, pointer_width: u32) -> Option<IntLit> {
        if !matches!(pointer_width, 32 | 64) {
            return None;
        }
        let nonnegative = |magnitude| IntLit {
            negative: false,
            magnitude,
        };
        match self {
            Self::WordBits => Some(nonnegative(u128::from(pointer_width))),
            Self::Minimum(range)
                if range.is_valid() && range.is_bounded() && range != crate::IntRange::Char =>
            {
                range.min(pointer_width).map(|value| IntLit {
                    negative: value < 0,
                    magnitude: value.unsigned_abs(),
                })
            }
            Self::Maximum(range)
                if range.is_valid() && range.is_bounded() && range != crate::IntRange::Char =>
            {
                range.max(pointer_width).map(nonnegative)
            }
            Self::Bits(range)
                if range.is_valid() && range.is_bounded() && range != crate::IntRange::Char =>
            {
                range
                    .bits(pointer_width)
                    .map(|bits| nonnegative(u128::from(bits)))
            }
            _ => None,
        }
    }
}

/// Binary operators. See the module documentation for arithmetic semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    /// `+`.
    Add,
    /// `-`.
    Sub,
    /// `*`.
    Mul,
    /// `/`: Euclidean on `int`/`nat`, truncating on machine types.
    Div,
    /// `%`: Euclidean on `int`/`nat`, truncating on machine types.
    Rem,
    /// `==`, on operands of the same type.
    Eq,
    /// `!=`, on operands of the same type.
    Ne,
    /// `<`, on integers of the same type.
    Lt,
    /// `<=`.
    Le,
    /// `>`.
    Gt,
    /// `>=`.
    Ge,
    /// `&&`.
    And,
    /// `||`.
    Or,
    /// `==>`.
    Implies,
    /// `&` on `bool` or on machine integers of one type.
    BitAnd,
    /// `|` on `bool` or on machine integers of one type.
    BitOr,
    /// `^` on `bool` or on machine integers of one type.
    BitXor,
    /// `<<` on machine integers.
    Shl,
    /// `>>` on machine integers.
    Shr,
}

impl BinOp {
    /// `+ - * / %`.
    #[must_use]
    pub const fn is_arithmetic(self) -> bool {
        matches!(
            self,
            Self::Add | Self::Sub | Self::Mul | Self::Div | Self::Rem
        )
    }

    /// `== != < <= > >=`.
    #[must_use]
    pub const fn is_comparison(self) -> bool {
        matches!(
            self,
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge
        )
    }

    /// `&& || ==>`.
    #[must_use]
    pub const fn is_logical(self) -> bool {
        matches!(self, Self::And | Self::Or | Self::Implies)
    }

    /// `& | ^`.
    #[must_use]
    pub const fn is_bitwise(self) -> bool {
        matches!(self, Self::BitAnd | Self::BitOr | Self::BitXor)
    }

    /// `<< >>`.
    #[must_use]
    pub const fn is_shift(self) -> bool {
        matches!(self, Self::Shl | Self::Shr)
    }
}

/// How a cast changes a value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CastKind {
    /// The value is unchanged. Only between integer types whose target range
    /// contains the source range (`u8` to `int`, `u32` to `u64`, `nat` to
    /// `int`); the checker enforces this.
    Exact,
    /// An `as` cast between integer types. A value that fits the target is
    /// kept; any other value becomes some value of the target type, fixed for
    /// that input. This is Verus's reading of `as`; Rust's truncation is one
    /// such function, so everything proved about it holds for the compiled
    /// code.
    As,
}

/// An expression with its type and source position.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    /// The type of the value.
    pub ty: Ty,
    /// Source position.
    pub span: SpanId,
    /// The expression itself.
    pub kind: ExprKind,
}

/// Expression forms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    /// A literal.
    Lit(Lit),
    /// An exact source primitive/architecture constant, never host-evaluated.
    IntegerConstant(IntegerConstant),
    /// The current value of a place.
    Read(Place),
    /// The value a place had on entry to the function (Verus `old`). The
    /// root must be a parameter.
    Old(Place),
    /// A unary operation.
    Unary {
        /// The operator.
        op: UnOp,
        /// The operand.
        arg: Box<Expr>,
        /// Exec check site; see the module documentation.
        check: Option<SiteId>,
    },
    /// A binary operation.
    Binary {
        /// The operator.
        op: BinOp,
        /// Left operand.
        lhs: Box<Expr>,
        /// Right operand.
        rhs: Box<Expr>,
        /// Exec check site; see the module documentation.
        check: Option<SiteId>,
    },
    /// `if cond { then_expr } else { else_expr }`.
    If {
        /// The condition.
        cond: Box<Expr>,
        /// Value when the condition holds.
        then_expr: Box<Expr>,
        /// Value otherwise.
        else_expr: Box<Expr>,
    },
    /// `let local = value; body` in spec code. The local has kind
    /// [`crate::LocalKind::Bound`].
    Let {
        /// The bound local.
        local: LocalId,
        /// Its value.
        value: Box<Expr>,
        /// The expression it is visible in.
        body: Box<Expr>,
    },
    /// A call of a spec function.
    Call {
        /// The callee; its mode must be spec.
        callee: FnId,
        /// One type per type parameter of the callee; its parameter and
        /// result types are read with them.
        type_args: Vec<Ty>,
        /// Arguments, one per parameter.
        args: Vec<Expr>,
    },
    /// A cast between integer types; the target is the node's type.
    Cast {
        /// The value cast.
        arg: Box<Expr>,
        /// What the cast does to it.
        kind: CastKind,
    },
    /// A struct or enum value.
    Ctor {
        /// The type constructed; equals the node's type.
        adt: AdtId,
        /// Variant index; 0 for a struct.
        variant: u32,
        /// One value per field of the variant, in declaration order.
        fields: Vec<Expr>,
    },
    /// Test the actual variant of a typed enum value.
    IsVariant {
        /// The enum value, possibly behind shared references.
        base: Box<Expr>,
        /// Index in its admitted declaration.
        variant: u32,
    },
    /// A tuple value.
    Tuple(Vec<Expr>),
    /// A field of a struct or enum value.
    Field {
        /// The value projected.
        base: Box<Expr>,
        /// Variant index; 0 for a struct.
        variant: u32,
        /// Field index.
        field: u32,
    },
    /// An element of a tuple value.
    TupleField {
        /// The tuple.
        base: Box<Expr>,
        /// Element index.
        index: u32,
    },
    /// A shared reference to a value (`&e`); the node's type is
    /// `Ref { mutable: false, .. }` of the operand's type. Shared references
    /// are transparent: the value is the operand's.
    Borrow(Box<Expr>),
    /// A `proof { .. }` block in the body of a spec function with a
    /// measure (Verus's `ProofInSpec`), of type `()`. Its statements are
    /// proof code that only the function's termination check walks, where
    /// Verus evaluates it; the function's definition ignores it. A producer
    /// sequences it with a `Let` of a `()` local.
    ProofInSpec(crate::stmt::Block),
    /// `forall|vars| body` or `exists|vars| body`, of type `bool`. Each var
    /// is a local of kind [`crate::LocalKind::Bound`] bound only here, and
    /// ranges over the values of its type, as in Verus (a `u8` over
    /// `0..=255`, a `nat` over the non-negative integers).
    ///
    /// `triggers` are Verus's triggers for the quantifier, as Verus chooses
    /// them (`crate::triggers`): one or more groups of terms, each group
    /// mentioning every var. They are part of the meaning for verification:
    /// the VC generator instantiates a quantified fact only where Verus's
    /// solver would (see `crate::vcgen`), so that nothing is proved that
    /// Verus does not prove.
    Quant {
        /// Forall or exists.
        kind: QuantKind,
        /// The bound locals with their types, in order.
        vars: Vec<(LocalId, Ty)>,
        /// Trigger groups.
        triggers: Vec<Vec<Expr>>,
        /// The quantified condition.
        body: Box<Expr>,
    },
    /// `choose|vars| cond`: the value of `result` at values of the vars
    /// that satisfy `cond`, when some do; otherwise some value of the type.
    /// `result` reads the single var, or is the tuple of the vars
    /// (`choose_tuple`). The vars are bound as in [`ExprKind::Quant`], and
    /// `triggers` are the triggers of `exists|vars| cond`.
    ///
    /// As in Verus (AIR's closures), the value is a function of the
    /// expression's holes: its maximal subexpressions that mention no local
    /// bound inside it. Two `Choose` expressions that are equal up to their
    /// holes choose the same value where their holes are equal; any other
    /// two are unrelated.
    Choose {
        /// The bound locals with their types, in order.
        vars: Vec<(LocalId, Ty)>,
        /// Trigger groups of `exists|vars| cond`.
        triggers: Vec<Vec<Expr>>,
        /// The condition.
        cond: Box<Expr>,
        /// The value chosen.
        result: Box<Expr>,
    },
    /// A fully typed source binder whose trigger inference failed. This is
    /// diagnostic data, never executable IR. It preserves the real body and
    /// explicit trigger candidates so earlier type/mode errors remain visible.
    /// Ordinary well-formedness and VC generation always reject it.
    UntriggeredQuant {
        /// The original quantifier kind.
        kind: QuantKind,
        /// Original typed bound locals.
        vars: Vec<(LocalId, Ty)>,
        /// Explicit source candidates, without claiming valid trigger groups.
        trigger_candidates: Vec<Expr>,
        /// The original typed condition.
        body: Box<Expr>,
    },
    /// The diagnostic-only counterpart of `Choose`, with its genuine
    /// condition and result rather than a fabricated value or declaration.
    UntriggeredChoose {
        /// Original typed bound locals.
        vars: Vec<(LocalId, Ty)>,
        /// Explicit source candidates, without claiming valid trigger groups.
        trigger_candidates: Vec<Expr>,
        /// The original typed condition.
        cond: Box<Expr>,
        /// The original typed value expression.
        result: Box<Expr>,
    },
}

/// Which quantifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum QuantKind {
    /// `forall`.
    Forall,
    /// `exists`.
    Exists,
}

impl Expr {
    /// An expression from its parts.
    #[must_use]
    pub const fn new(ty: Ty, span: SpanId, kind: ExprKind) -> Self {
        Self { ty, span, kind }
    }

    /// A `bool` literal.
    #[must_use]
    pub const fn bool_lit(value: bool, span: SpanId) -> Self {
        Self::new(Ty::Bool, span, ExprKind::Lit(Lit::Bool(value)))
    }

    /// An integer literal of type `ty`.
    #[must_use]
    pub const fn int_lit(value: i128, ty: Ty, span: SpanId) -> Self {
        Self::new(ty, span, ExprKind::Lit(Lit::Int(IntLit::from_i128(value))))
    }

    /// The current value of `place`, of type `ty`.
    #[must_use]
    pub const fn read(place: Place, ty: Ty, span: SpanId) -> Self {
        Self::new(ty, span, ExprKind::Read(place))
    }

    /// A spec (unchecked) binary operation.
    #[must_use]
    pub fn binary(op: BinOp, lhs: Self, rhs: Self, ty: Ty, span: SpanId) -> Self {
        Self::new(
            ty,
            span,
            ExprKind::Binary {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                check: None,
            },
        )
    }

    /// An exec binary operation checked at `site`.
    #[must_use]
    pub fn checked_binary(
        op: BinOp,
        lhs: Self,
        rhs: Self,
        ty: Ty,
        site: SiteId,
        span: SpanId,
    ) -> Self {
        Self::new(
            ty,
            span,
            ExprKind::Binary {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                check: Some(site),
            },
        )
    }

    /// A cast of `self` to `ty`.
    #[must_use]
    pub fn cast(self, kind: CastKind, ty: Ty, span: SpanId) -> Self {
        Self::new(
            ty,
            span,
            ExprKind::Cast {
                arg: Box::new(self),
                kind,
            },
        )
    }

    /// Call `f` on each direct subexpression, in evaluation order: the
    /// operands, branches and arguments; a quantifier's or choice's trigger
    /// terms before its body. The statements of a [`ExprKind::ProofInSpec`]
    /// block are not expressions of this one and are not visited.
    pub fn for_each_child<'e>(&'e self, f: &mut dyn FnMut(&'e Self)) {
        match &self.kind {
            ExprKind::Lit(_)
            | ExprKind::IntegerConstant(_)
            | ExprKind::Read(_)
            | ExprKind::Old(_)
            | ExprKind::ProofInSpec(_) => {}
            ExprKind::Unary { arg, .. } | ExprKind::Cast { arg, .. } => f(arg),
            ExprKind::Binary { lhs, rhs, .. } => {
                f(lhs);
                f(rhs);
            }
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                f(cond);
                f(then_expr);
                f(else_expr);
            }
            ExprKind::Let { value, body, .. } => {
                f(value);
                f(body);
            }
            ExprKind::Call { args, .. }
            | ExprKind::Ctor { fields: args, .. }
            | ExprKind::Tuple(args) => {
                for arg in args {
                    f(arg);
                }
            }
            ExprKind::Field { base, .. }
            | ExprKind::IsVariant { base, .. }
            | ExprKind::TupleField { base, .. }
            | ExprKind::Borrow(base) => f(base),
            ExprKind::Quant { triggers, body, .. } => {
                for term in triggers.iter().flatten() {
                    f(term);
                }
                f(body);
            }
            ExprKind::Choose {
                triggers,
                cond,
                result,
                ..
            } => {
                for term in triggers.iter().flatten() {
                    f(term);
                }
                f(cond);
                f(result);
            }
            ExprKind::UntriggeredQuant {
                trigger_candidates,
                body,
                ..
            } => {
                for term in trigger_candidates {
                    f(term);
                }
                f(body);
            }
            ExprKind::UntriggeredChoose {
                trigger_candidates,
                cond,
                result,
                ..
            } => {
                for term in trigger_candidates {
                    f(term);
                }
                f(cond);
                f(result);
            }
        }
    }

    /// Does `pred` hold for `self` or any expression inside it (not
    /// looking into proof blocks)?
    #[must_use]
    pub fn any(&self, pred: &dyn Fn(&Self) -> bool) -> bool {
        if pred(self) {
            return true;
        }
        let mut found = false;
        self.for_each_child(&mut |child| {
            found = found || child.any(pred);
        });
        found
    }

    /// The expression with every local in `map` replaced by its image: the
    /// roots of `Read` and `Old` and the locals bound by `Let`, `Quant` and
    /// `Choose`. The statements of a proof block are kept as they are.
    #[must_use]
    pub fn rename_locals(&self, map: &std::collections::HashMap<LocalId, LocalId>) -> Self {
        let local = |id: &LocalId| *map.get(id).unwrap_or(id);
        let place = |p: &Place| Place {
            local: local(&p.local),
            projections: p.projections.clone(),
        };
        let b = |e: &Self| Box::new(e.rename_locals(map));
        let all = |es: &[Self]| es.iter().map(|e| e.rename_locals(map)).collect::<Vec<_>>();
        let groups = |gs: &[Vec<Self>]| gs.iter().map(|g| all(g)).collect::<Vec<_>>();
        let kind = match &self.kind {
            ExprKind::Lit(lit) => ExprKind::Lit(*lit),
            ExprKind::IntegerConstant(value) => ExprKind::IntegerConstant(*value),
            ExprKind::Read(p) => ExprKind::Read(place(p)),
            ExprKind::Old(p) => ExprKind::Old(place(p)),
            ExprKind::Unary { op, arg, check } => ExprKind::Unary {
                op: *op,
                arg: b(arg),
                check: *check,
            },
            ExprKind::Binary {
                op,
                lhs,
                rhs,
                check,
            } => ExprKind::Binary {
                op: *op,
                lhs: b(lhs),
                rhs: b(rhs),
                check: *check,
            },
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => ExprKind::If {
                cond: b(cond),
                then_expr: b(then_expr),
                else_expr: b(else_expr),
            },
            ExprKind::Let {
                local: bound,
                value,
                body,
            } => ExprKind::Let {
                local: local(bound),
                value: b(value),
                body: b(body),
            },
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => ExprKind::Call {
                callee: *callee,
                type_args: type_args.clone(),
                args: all(args),
            },
            ExprKind::Cast { arg, kind } => ExprKind::Cast {
                arg: b(arg),
                kind: *kind,
            },
            ExprKind::Ctor {
                adt,
                variant,
                fields,
            } => ExprKind::Ctor {
                adt: *adt,
                variant: *variant,
                fields: all(fields),
            },
            ExprKind::IsVariant { base, variant } => ExprKind::IsVariant {
                base: b(base),
                variant: *variant,
            },
            ExprKind::Tuple(elems) => ExprKind::Tuple(all(elems)),
            ExprKind::Field {
                base,
                variant,
                field,
            } => ExprKind::Field {
                base: b(base),
                variant: *variant,
                field: *field,
            },
            ExprKind::TupleField { base, index } => ExprKind::TupleField {
                base: b(base),
                index: *index,
            },
            ExprKind::Borrow(inner) => ExprKind::Borrow(b(inner)),
            ExprKind::ProofInSpec(block) => ExprKind::ProofInSpec(block.clone()),
            ExprKind::Quant {
                kind,
                vars,
                triggers,
                body,
            } => ExprKind::Quant {
                kind: *kind,
                vars: vars.iter().map(|(v, t)| (local(v), t.clone())).collect(),
                triggers: groups(triggers),
                body: b(body),
            },
            ExprKind::Choose {
                vars,
                triggers,
                cond,
                result,
            } => ExprKind::Choose {
                vars: vars.iter().map(|(v, t)| (local(v), t.clone())).collect(),
                triggers: groups(triggers),
                cond: b(cond),
                result: b(result),
            },
            ExprKind::UntriggeredQuant {
                kind,
                vars,
                trigger_candidates,
                body,
            } => ExprKind::UntriggeredQuant {
                kind: *kind,
                vars: vars.iter().map(|(v, t)| (local(v), t.clone())).collect(),
                trigger_candidates: all(trigger_candidates),
                body: b(body),
            },
            ExprKind::UntriggeredChoose {
                vars,
                trigger_candidates,
                cond,
                result,
            } => ExprKind::UntriggeredChoose {
                vars: vars.iter().map(|(v, t)| (local(v), t.clone())).collect(),
                trigger_candidates: all(trigger_candidates),
                cond: b(cond),
                result: b(result),
            },
        };
        Self::new(self.ty.clone(), self.span, kind)
    }

    /// A logical negation of `self`.
    #[must_use]
    pub fn not(self, span: SpanId) -> Self {
        Self::new(
            Ty::Bool,
            span,
            ExprKind::Unary {
                op: UnOp::Not,
                arg: Box::new(self),
                check: None,
            },
        )
    }
}
