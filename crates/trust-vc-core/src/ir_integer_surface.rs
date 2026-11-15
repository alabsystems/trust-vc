//! The integer-typing surface of the expression IR, stated as DATA.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Exists so the integer-typing oracle (`tests/integer_typing_oracle.rs`) is
//! MECHANICALLY complete rather than complete by review. Integer-typing
//! defects kept reappearing in constructs the property tests did not generate
//! (a `match` arm widened by the match's sign, a call argument bound at a
//! type that cannot hold it, a `let` re-reading its value's bits); a list of
//! "shapes we thought of" is exactly what missed them.
//!
//! [`EXPR_VARIANTS`] and [`expr_variant`] are generated from ONE exhaustive
//! `match` over [`TrustVcExpr`] (no wildcard; the enum is `non_exhaustive`, so
//! only this crate can write it): a new variant does not compile until it is
//! classified here, and once it is classified with an integer role the
//! oracle's coverage test fails until the oracle generates it and decides at
//! least one goal through it (design-trust-proof-backend.md §5b).

use crate::ir::TrustVcExpr;

/// How an expression variant takes part in integer typing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntegerRole {
    /// An integer leaf (literal, variable, associated constant) or an integer
    /// computed from its operands: its type is DERIVED (§5b rule 1), its
    /// value is fixed by its operands.
    Produces,
    /// Its value is one of its subterms (a conditional, a `match`): every
    /// branch denotes the integer it holds, widened by ITS OWN sign.
    Joins,
    /// Binds a value at a DECLARED integer type — a `let`, a call argument or
    /// a spec function's result, an operand of a `wrapping_*` method, a
    /// collection element, a `choose` or quantifier binder (§5b rules 3, 6).
    Binds,
    /// Compares integers: over the integers the operands denote (rules 1, 4).
    Compares,
    /// An integer the operands do not determine (a fresh prophecy, a read of
    /// a memory place, its resolution): typed like a variable, with no value
    /// an oracle could compute from the expression.
    Opaque,
    /// No integer semantics.
    None,
}

macro_rules! expr_variants {
    ($($variant:ident => [$($role:ident),* $(,)?]),* $(,)?) => {
        /// Every [`TrustVcExpr`] variant, by name, with its integer roles.
        ///
        /// Generated from the same exhaustive `match` as [`expr_variant`], so
        /// it cannot omit a variant.
        pub const EXPR_VARIANTS: &[(&str, &[IntegerRole])] = &[
            $((stringify!($variant), &[$(IntegerRole::$role),*])),*
        ];

        /// The variant name of `expr` (one of [`EXPR_VARIANTS`]).
        #[must_use]
        pub fn expr_variant(expr: &TrustVcExpr) -> &'static str {
            match expr {
                $(TrustVcExpr::$variant { .. } => stringify!($variant)),*
            }
        }
    };
}

expr_variants! {
    UnitLit => [None],
    BoolLit => [None],
    StringLit => [None],
    IntLit => [Produces],
    Var => [Produces],
    Arith => [Produces],
    Neg => [Produces],
    Compare => [Compares],
    Logic => [None],
    // `!x` of an integer is the bitwise complement in `x`'s type.
    Not => [Produces],
    Implies => [None],
    Ite => [Joins],
    Match => [Joins],
    Let => [Binds],
    Cast => [Produces],
    // `len`/`count`/`first`/… produce integers; `push`/`insert`/`update`
    // bind an element at the collection's element type.
    CollectionOp => [Produces, Binds],
    Index => [Produces],
    Quantifier => [Binds],
    // A spec function's result is bound at its declared result type, its
    // arguments at its parameters' types.
    FnCall => [Produces, Binds],
    // A closure VALUE; its application is a `FnCall`.
    SpecClosure => [None],
    IntConst => [Produces],
    SpecialArith => [Produces],
    WrappingArith => [Produces, Binds],
    Choose => [Produces, Binds],
    ReadPlace => [Opaque],
    PlaceDisjoint => [None],
    ProphecyNew => [Opaque],
    ProphecyResolve => [Opaque],
}

/// The variant name of every node of `expr` (pre-order, with repetitions):
/// what an oracle reads to know which variants a generated goal exercised.
#[must_use]
pub fn expr_variants_in(expr: &TrustVcExpr) -> Vec<&'static str> {
    struct Collect(Vec<&'static str>);
    impl crate::ir_expr_traversal::TrustVcExprVisitor for Collect {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            self.0.push(expr_variant(expr));
            crate::ir_expr_traversal::walk_expr(self, expr);
        }
    }
    let mut collect = Collect(Vec::new());
    crate::ir_expr_traversal::TrustVcExprVisitor::visit_expr(&mut collect, expr);
    collect.0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::TrustVcType;

    #[test]
    fn every_variant_is_listed_once() {
        let mut names: Vec<&str> = EXPR_VARIANTS.iter().map(|(name, _)| *name).collect();
        let total = names.len();
        names.sort_unstable();
        names.dedup();
        assert_eq!(names.len(), total, "a variant is listed twice");
        assert!(EXPR_VARIANTS.iter().all(|(_, roles)| !roles.is_empty()));
    }

    #[test]
    fn walking_names_every_node() {
        let x = TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Uint { width: 8 },
        };
        let e = TrustVcExpr::Neg(Box::new(TrustVcExpr::Cast {
            expr: Box::new(x),
            from_ty: TrustVcType::Uint { width: 8 },
            to_ty: TrustVcType::Int { width: 16 },
        }));
        assert_eq!(expr_variants_in(&e), vec!["Neg", "Cast", "Var"]);
    }
}
