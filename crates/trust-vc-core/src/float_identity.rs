//! Equations the lane writes to say two terms are the same value.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! A float `==` is IEEE 754 equality: `NaN == NaN` is false and
//! `0.0 == -0.0` is true. The lane also writes `==` for equations it makes
//! itself, to say that two terms denote one value: the binding of a function's
//! return value, the definition of a function by its body, the frame of a
//! variable a loop leaves alone, the value a loop body gives a variable. Read
//! as IEEE equality over floats, such an equation is false when the value is
//! NaN, so assuming it assumes the value is not NaN, which nothing in the
//! program guarantees. `fn f(x: f64) -> f64 { x }` then verified
//! `ensures(r == x)`, which fails for `f64::NAN`.
//!
//! [`identity_equation`] builds what such an equation must say over floats:
//! the two sides are IEEE-equal, or both are NaN. Every pair of identical
//! values satisfies it, so it assumes nothing the program does not guarantee.
//! It is weaker than identity only in letting `0.0` stand for `-0.0`, which
//! the IEEE reading already did. Over every other type it is the plain `==`.

use crate::ir::{CompareOp, LogicOp, TrustVcExpr, TrustVcType};

/// Whether an equation between `left` and `right` compares floats.
pub(crate) fn is_float_equation(left: &TrustVcExpr, right: &TrustVcExpr) -> bool {
    [left, right].into_iter().any(|side| {
        matches!(
            crate::ir_lowering::infer_expr_type(side),
            TrustVcType::Float { .. }
        )
    })
}

/// The equation "`left` and `right` are the same value".
///
/// Over floats: `left == right || (left != left && right != right)`.
pub(crate) fn identity_equation(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    if !is_float_equation(&left, &right) {
        return compare(CompareOp::Eq, left, right);
    }
    let both_nan = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(compare(CompareOp::Ne, left.clone(), left.clone())),
        right: Box::new(compare(CompareOp::Ne, right.clone(), right.clone())),
    };
    TrustVcExpr::Logic {
        op: LogicOp::Or,
        left: Box::new(compare(CompareOp::Eq, left, right)),
        right: Box::new(both_nan),
    }
}

/// The two sides of an equation [`identity_equation`] built, or of a plain
/// `==`.
pub(crate) fn identity_equation_sides(expr: &TrustVcExpr) -> Option<(&TrustVcExpr, &TrustVcExpr)> {
    match expr {
        TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left,
            right,
        } => Some((left, right)),
        TrustVcExpr::Logic {
            op: LogicOp::Or,
            left: equation,
            right: both_nan,
        } => {
            let TrustVcExpr::Compare {
                op: CompareOp::Eq,
                left,
                right,
            } = equation.as_ref()
            else {
                return None;
            };
            let TrustVcExpr::Logic {
                op: LogicOp::And,
                left: left_nan,
                right: right_nan,
            } = both_nan.as_ref()
            else {
                return None;
            };
            (is_float_equation(left, right)
                && is_self_disequality(left_nan, left)
                && is_self_disequality(right_nan, right))
            .then_some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

/// Reads each equation a lane-made definition or binding states as an
/// [`identity_equation`]: the expression itself when it is an `==`, each side
/// of a disjunction (a return value with several candidates), and the
/// conclusion of an implication (a definition under its precondition).
/// Anything else, including every comparison inside an equation's sides, is
/// left as written.
pub(crate) fn read_equations_as_identity(expr: TrustVcExpr) -> TrustVcExpr {
    if identity_equation_sides(&expr).is_some() && !matches!(expr, TrustVcExpr::Compare { .. }) {
        return expr;
    }
    match expr {
        TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left,
            right,
        } => identity_equation(*left, *right),
        TrustVcExpr::Logic {
            op: LogicOp::Or,
            left,
            right,
        } => TrustVcExpr::Logic {
            op: LogicOp::Or,
            left: Box::new(read_equations_as_identity(*left)),
            right: Box::new(read_equations_as_identity(*right)),
        },
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => TrustVcExpr::Implies {
            premise,
            conclusion: Box::new(read_equations_as_identity(*conclusion)),
        },
        other => other,
    }
}

fn compare(op: CompareOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn is_self_disequality(expr: &TrustVcExpr, operand: &TrustVcExpr) -> bool {
    matches!(
        expr,
        TrustVcExpr::Compare {
            op: CompareOp::Ne,
            left,
            right,
        } if left.as_ref() == operand && right.as_ref() == operand
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn float_var(name: &str) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty: TrustVcType::Float { width: 64 },
        }
    }

    fn u64_var(name: &str) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty: TrustVcType::Uint { width: 64 },
        }
    }

    #[test]
    fn a_float_equation_admits_two_nans() {
        let equation = identity_equation(float_var("r"), float_var("x"));
        let expected = TrustVcExpr::Logic {
            op: LogicOp::Or,
            left: Box::new(compare(CompareOp::Eq, float_var("r"), float_var("x"))),
            right: Box::new(TrustVcExpr::Logic {
                op: LogicOp::And,
                left: Box::new(compare(CompareOp::Ne, float_var("r"), float_var("r"))),
                right: Box::new(compare(CompareOp::Ne, float_var("x"), float_var("x"))),
            }),
        };
        assert_eq!(equation, expected);
        let (left, right) = identity_equation_sides(&equation).expect("sides");
        assert_eq!((left, right), (&float_var("r"), &float_var("x")));
    }

    #[test]
    fn an_integer_equation_is_the_plain_comparison() {
        let equation = identity_equation(u64_var("r"), u64_var("x"));
        assert_eq!(equation, compare(CompareOp::Eq, u64_var("r"), u64_var("x")));
        assert!(identity_equation_sides(&equation).is_some());
    }

    #[test]
    fn a_user_disjunction_is_not_read_as_an_equation() {
        // `r == x || (r != r && y != y)` names a third value: it is not the
        // identity of `r` and `x`.
        let expr = TrustVcExpr::Logic {
            op: LogicOp::Or,
            left: Box::new(compare(CompareOp::Eq, float_var("r"), float_var("x"))),
            right: Box::new(TrustVcExpr::Logic {
                op: LogicOp::And,
                left: Box::new(compare(CompareOp::Ne, float_var("r"), float_var("r"))),
                right: Box::new(compare(CompareOp::Ne, float_var("y"), float_var("y"))),
            }),
        };
        assert!(identity_equation_sides(&expr).is_none());
    }

    #[test]
    fn only_the_stated_equations_are_rewritten() {
        // `(r == a) || (r == b)` binds `r` to one of two candidates; the
        // comparison inside a candidate keeps its IEEE reading.
        let inner = compare(CompareOp::Eq, float_var("x"), float_var("x"));
        let candidate = TrustVcExpr::Ite {
            cond: Box::new(inner.clone()),
            then_branch: Box::new(float_var("a")),
            else_branch: Box::new(float_var("b")),
            ty: TrustVcType::Float { width: 64 },
        };
        let binding = TrustVcExpr::Logic {
            op: LogicOp::Or,
            left: Box::new(compare(CompareOp::Eq, float_var("r"), candidate.clone())),
            right: Box::new(compare(CompareOp::Eq, float_var("r"), float_var("b"))),
        };
        let read = read_equations_as_identity(binding);
        let expected = TrustVcExpr::Logic {
            op: LogicOp::Or,
            left: Box::new(identity_equation(float_var("r"), candidate)),
            right: Box::new(identity_equation(float_var("r"), float_var("b"))),
        };
        assert_eq!(read, expected);
        assert_eq!(read_equations_as_identity(read.clone()), read);
    }

    #[test]
    fn a_definition_under_a_precondition_rewrites_its_conclusion() {
        let premise = compare(CompareOp::Eq, float_var("p"), float_var("p"));
        let definition = TrustVcExpr::Implies {
            premise: Box::new(premise.clone()),
            conclusion: Box::new(compare(CompareOp::Eq, float_var("f"), float_var("x"))),
        };
        assert_eq!(
            read_equations_as_identity(definition),
            TrustVcExpr::Implies {
                premise: Box::new(premise),
                conclusion: Box::new(identity_equation(float_var("f"), float_var("x"))),
            }
        );
    }
}
