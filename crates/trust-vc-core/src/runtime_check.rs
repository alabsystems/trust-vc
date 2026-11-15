// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Which specification clauses the `trust_vc` macros evaluate at run time.
//!
//! Outside a verification build the macros check a `requires`, `ensures` or
//! `returns` clause, and the condition of `trust_vc::assert!`,
//! `assert_seqs_equal!`, `invariant!` and `invariant_except_break!`, with
//! `assert!`, and they evaluate the measure of `loop_decreases!`. The lane
//! reads every one of these as ghost code. A check whose run-time value can
//! differ from that reading makes a program the lane verifies panic:
//!
//! - a spec or proof function's body is `loop { unreachable!(..) }` outside a
//!   verification build, so a check that calls one panics on every run,
//!   whether it names the function or reaches it through an index
//!   (`Index::index`);
//! - `forall!`, `exists!` and `decreases_to!` evaluate to `true` there, which
//!   is wrong under a negation, and any other macro can call anything;
//! - the lane reads the `+`, `-`, `*` and negation of a `requires` over the
//!   mathematical integers (`spec_arith`), and a `loop_decreases!` measure in
//!   the integer lane, so `requires(z + 1u32 > z)` holds at `u32::MAX` while
//!   its run-time check overflows. The other clauses are read at fixed width,
//!   and each of their operations carries an overflow, division or shift
//!   obligation, so a verified check of them cannot panic in its arithmetic.
//!
//! The macros see one item's tokens and cannot tell a spec function from an
//! exec one, so a clause is evaluated at run time only when it calls nothing
//! (no call, method call, index or macro) and, in a clause read over the
//! integers, does no arithmetic. Any other clause is type-checked and never
//! evaluated.

use proc_macro2::TokenStream;
use quote::quote;
use syn::visit::Visit;

/// How the lane reads a clause's arithmetic.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClauseArithmetic {
    /// At fixed width, each operation with an obligation that it does not
    /// overflow, divide by zero or shift past the width: `ensures`, `returns`,
    /// `trust_vc::assert!` and the loop invariants.
    FixedWidthChecked,
    /// Over the mathematical integers: `requires` and a `loop_decreases!`
    /// measure.
    Integer,
}

/// Whether evaluating `expr` at run time can only give the value the lane
/// reads it as: it holds no call, method call, index, macro, `?`, `.await` or
/// token `syn` leaves unparsed, and, when read over the integers, no
/// arithmetic operator.
#[doc(hidden)]
pub fn runtime_check_evaluates_as_read(expr: &syn::Expr, arithmetic: ClauseArithmetic) -> bool {
    let mut finder = RuntimeDivergenceFinder {
        arithmetic,
        found: false,
    };
    finder.visit_expr(expr);
    !finder.found
}

/// `check` when `clause` passes [`runtime_check_evaluates_as_read`];
/// otherwise a branch that is never taken, so `clause` is type-checked and
/// borrow-checked where `check` would have been and never evaluated. A clause
/// that does not parse is never evaluated either.
#[doc(hidden)]
pub fn runtime_check_or_typecheck(
    clause: &TokenStream,
    arithmetic: ClauseArithmetic,
    check: TokenStream,
) -> TokenStream {
    let evaluates_as_read = syn::parse2::<syn::Expr>(clause.clone())
        .is_ok_and(|expr| runtime_check_evaluates_as_read(&expr, arithmetic));
    if evaluates_as_read {
        check
    } else {
        quote! {
            if false {
                let _ = { #clause };
            }
        }
    }
}

struct RuntimeDivergenceFinder {
    arithmetic: ClauseArithmetic,
    found: bool,
}

impl<'ast> Visit<'ast> for RuntimeDivergenceFinder {
    fn visit_expr(&mut self, expr: &'ast syn::Expr) {
        if self.found {
            return;
        }
        let integer = self.arithmetic == ClauseArithmetic::Integer;
        match expr {
            syn::Expr::Call(_)
            | syn::Expr::MethodCall(_)
            | syn::Expr::Index(_)
            | syn::Expr::Macro(_)
            | syn::Expr::Try(_)
            | syn::Expr::Await(_)
            | syn::Expr::Verbatim(_) => self.found = true,
            syn::Expr::Binary(binary) if integer && is_arithmetic(&binary.op) => {
                self.found = true;
            }
            syn::Expr::Unary(unary)
                if integer && matches!(unary.op, syn::UnOp::Neg(_)) && !is_literal(&unary.expr) =>
            {
                self.found = true;
            }
            _ => syn::visit::visit_expr(self, expr),
        }
    }

    fn visit_macro(&mut self, _mac: &'ast syn::Macro) {
        self.found = true;
    }
}

fn is_arithmetic(op: &syn::BinOp) -> bool {
    matches!(
        op,
        syn::BinOp::Add(_)
            | syn::BinOp::Sub(_)
            | syn::BinOp::Mul(_)
            | syn::BinOp::Div(_)
            | syn::BinOp::Rem(_)
            | syn::BinOp::Shl(_)
            | syn::BinOp::Shr(_)
            | syn::BinOp::AddAssign(_)
            | syn::BinOp::SubAssign(_)
            | syn::BinOp::MulAssign(_)
            | syn::BinOp::DivAssign(_)
            | syn::BinOp::RemAssign(_)
            | syn::BinOp::ShlAssign(_)
            | syn::BinOp::ShrAssign(_)
    )
}

fn is_literal(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Lit(_) => true,
        syn::Expr::Paren(paren) => is_literal(&paren.expr),
        syn::Expr::Group(group) => is_literal(&group.expr),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn evaluates(clause: &str, arithmetic: ClauseArithmetic) -> bool {
        let expr: syn::Expr = syn::parse_str(clause).expect("clause should parse");
        runtime_check_evaluates_as_read(&expr, arithmetic)
    }

    #[test]
    fn a_clause_that_calls_nothing_is_evaluated() {
        for clause in [
            "ret > 0",
            "r == x",
            "x < 100u64 && y != 0u64",
            "s.a == old_s_a",
            "*x == 5u64",
            "(x as u8) == 3u8",
            "!(a || b)",
            "r == -1i64",
            "t.0 == (1u64, 2u64).1",
        ] {
            for arithmetic in [
                ClauseArithmetic::FixedWidthChecked,
                ClauseArithmetic::Integer,
            ] {
                assert!(
                    evaluates(clause, arithmetic),
                    "`{clause}` calls nothing and should be evaluated ({arithmetic:?})"
                );
            }
        }
    }

    #[test]
    fn a_clause_that_can_call_a_function_is_never_evaluated() {
        for clause in [
            "r == inc(x)",
            "m::inc(x) > x",
            "s.view() == s.a",
            "S::view(s) == 0u64",
            "v[i] == 0u64",
            "x > 0 && (y == 0 || f(y))",
            "forall!(|i: u64| i < 5u64)",
            "!exists!(|i: u64| i > 5u64)",
            "__trust_vc_implies!(a, b)",
            "{ let k = inc(x); k > x }",
            "{ g!(); true }",
            "x? > 0",
            "r == Some(x)",
        ] {
            for arithmetic in [
                ClauseArithmetic::FixedWidthChecked,
                ClauseArithmetic::Integer,
            ] {
                assert!(
                    !evaluates(clause, arithmetic),
                    "`{clause}` can call a function and should not be evaluated ({arithmetic:?})"
                );
            }
        }
    }

    #[test]
    fn arithmetic_is_evaluated_only_where_the_lane_checks_it() {
        for clause in [
            "z + 1u32 > z",
            "r == x - 1u64",
            "r == x * 2u64",
            "r == x / y",
            "r == x % y",
            "r == x << 2u32",
            "r == x >> 2u32",
            "r == -x",
            "r == -(x)",
        ] {
            assert!(
                evaluates(clause, ClauseArithmetic::FixedWidthChecked),
                "`{clause}` is checked at fixed width and should be evaluated"
            );
            assert!(
                !evaluates(clause, ClauseArithmetic::Integer),
                "`{clause}` is read over the integers and should not be evaluated"
            );
        }
    }

    #[test]
    fn a_clause_left_unevaluated_is_still_type_checked() {
        let emitted = runtime_check_or_typecheck(
            &quote! { r == inc(x) },
            ClauseArithmetic::FixedWidthChecked,
            quote! { assert!(r == inc(x)); },
        )
        .to_string();
        assert_eq!(emitted, "if false { let _ = { r == inc (x) } ; }");

        let kept = runtime_check_or_typecheck(
            &quote! { r > x },
            ClauseArithmetic::Integer,
            quote! { assert!(r > x); },
        )
        .to_string();
        assert_eq!(kept, "assert ! (r > x) ;");

        let unparsed = runtime_check_or_typecheck(
            &quote! { r > },
            ClauseArithmetic::FixedWidthChecked,
            quote! { assert!(r >); },
        )
        .to_string();
        assert!(unparsed.starts_with("if false"), "got: {unparsed}");
    }
}
