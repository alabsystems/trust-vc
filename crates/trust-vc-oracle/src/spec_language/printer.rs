// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ---------------------------------------------------------------------------
// SpecPrinter
// ---------------------------------------------------------------------------

/// Pretty-prints `SpecExpr` values back to text.
pub struct SpecPrinter;

impl SpecPrinter {
    /// Render a `SpecExpr` as a human-readable string.
    #[must_use]
    pub fn to_string(expr: &SpecExpr) -> String {
        Self::fmt_expr(expr, 0)
    }

    /// Render a `SpecClause` as a human-readable string.
    #[must_use]
    pub fn clause_to_string(clause: &SpecClause) -> String {
        match clause {
            SpecClause::Requires(e) => format!("requires {}", Self::to_string(e)),
            SpecClause::Ensures(e) => format!("ensures {}", Self::to_string(e)),
            SpecClause::Invariant(e) => format!("invariant {}", Self::to_string(e)),
            SpecClause::Decreases(e) => format!("decreases {}", Self::to_string(e)),
        }
    }

    /// Render a full `FunctionSpec`.
    #[must_use]
    pub fn function_spec_to_string(spec: &FunctionSpec) -> String {
        let mut out = String::new();
        out.push_str("fn ");
        out.push_str(&spec.name);
        out.push('(');
        for (i, (pname, ptype)) in spec.params.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            out.push_str(pname);
            out.push_str(": ");
            out.push_str(ptype);
        }
        out.push(')');
        if let Some(rt) = &spec.return_type {
            out.push_str(" -> ");
            out.push_str(rt);
        }
        for clause in &spec.clauses {
            out.push_str("\n  ");
            out.push_str(&Self::clause_to_string(clause));
        }
        out
    }

    // Precedence levels for parenthesization:
    //   0 = top (implies)
    //   1 = or
    //   2 = and
    //   3 = compare
    //   4 = additive
    //   5 = multiplicative
    //   6 = unary / atomic

    fn fmt_expr(expr: &SpecExpr, parent_prec: u8) -> String {
        match expr {
            SpecExpr::Variable(name) => name.clone(),
            SpecExpr::IntLit(n) => n.to_string(),
            SpecExpr::BoolLit(b) => b.to_string(),
            SpecExpr::BinOp(lhs, op, rhs) => {
                let (prec, sym) = Self::binop_info(*op);
                let s = format!(
                    "{} {} {}",
                    Self::fmt_expr(lhs, prec),
                    sym,
                    Self::fmt_expr(rhs, prec + 1)
                );
                if prec < parent_prec {
                    format!("({s})")
                } else {
                    s
                }
            }
            SpecExpr::UnaryOp(op, inner) => {
                let sym = match op {
                    UnaryOpKind::Not => "!",
                    UnaryOpKind::Neg => "-",
                };
                format!("{sym}{}", Self::fmt_expr(inner, 6))
            }
            SpecExpr::FnCall(name, args) => {
                let arg_strs: Vec<String> = args.iter().map(|a| Self::fmt_expr(a, 0)).collect();
                format!("{}({})", name, arg_strs.join(", "))
            }
            SpecExpr::Quantifier(kind, bindings, body) => {
                let kw = match kind {
                    QuantKind::Forall => "forall",
                    QuantKind::Exists => "exists",
                };
                let bindings_str: Vec<String> =
                    bindings.iter().map(|(n, t)| format!("{n}: {t}")).collect();
                let s = format!(
                    "{} {} :: {}",
                    kw,
                    bindings_str.join(", "),
                    Self::fmt_expr(body, 0)
                );
                if parent_prec > 0 {
                    format!("({s})")
                } else {
                    s
                }
            }
            SpecExpr::FieldAccess(base, field) => {
                format!("{}.{field}", Self::fmt_expr(base, 6))
            }
            SpecExpr::IndexAccess(base, index) => {
                format!("{}[{}]", Self::fmt_expr(base, 6), Self::fmt_expr(index, 0))
            }
            SpecExpr::IfThenElse(cond, then_br, else_br) => {
                let s = format!(
                    "if {} then {} else {}",
                    Self::fmt_expr(cond, 0),
                    Self::fmt_expr(then_br, 0),
                    Self::fmt_expr(else_br, 0)
                );
                if parent_prec > 0 {
                    format!("({s})")
                } else {
                    s
                }
            }
            SpecExpr::Old(inner) => format!("old({})", Self::fmt_expr(inner, 0)),
        }
    }

    fn binop_info(op: BinOpKind) -> (u8, &'static str) {
        match op {
            BinOpKind::Implies => (0, "==>"),
            BinOpKind::Or => (1, "||"),
            BinOpKind::And => (2, "&&"),
            BinOpKind::Eq => (3, "=="),
            BinOpKind::Ne => (3, "!="),
            BinOpKind::Lt => (3, "<"),
            BinOpKind::Le => (3, "<="),
            BinOpKind::Gt => (3, ">"),
            BinOpKind::Ge => (3, ">="),
            BinOpKind::Add => (4, "+"),
            BinOpKind::Sub => (4, "-"),
            BinOpKind::Mul => (5, "*"),
            BinOpKind::Div => (5, "/"),
            BinOpKind::Mod => (5, "%"),
        }
    }
}
