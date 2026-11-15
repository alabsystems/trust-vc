//! Rust protocol bodies to TLA+, over a closed and typed subset.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! An `#[action]` or `#[safety]` body is parsed with `syn`, typed against the
//! protocol's state variables and translated construct by construct. An
//! action is early returns `if <bool> { return; }` followed by assignments
//! `self.field = value`; a safety body is one `bool` expression. Only a
//! construct whose TLA+ reading equals its Rust reading is admitted: `bool`
//! and fixed-width integer fields, integer and `bool` literals, `!` on a
//! `bool`, `-` on a signed integer, `&&`, `||`, `==`, `!=`, `<`, `<=`, `>`,
//! `>=`, `+`, `-` and `*`. Everything else is refused, in particular `^` (XOR
//! in Rust, a power in TLA+), `/` and `%` (truncating in Rust, not in TLA+),
//! `!` on an integer (bitwise in Rust), shifts, bit operators, casts, calls,
//! macros and attributes.
//!
//! A Rust integer has a width and a TLA+ integer does not, so a translated
//! expression is a pair: its `value` under exact arithmetic, and `defined`,
//! the condition under which Rust evaluates it without overflowing, which
//! follows the short-circuiting of `&&` and `||`. Where `defined` holds,
//! `value` is the Rust value. The caller turns a state where it does not hold
//! into a violation, never into a transition that is skipped.

use crate::verification_bridge::ProtocolValue;
use quote::ToTokens;
use syn::{BinOp, Expr, ExprBinary, Lit, Member, Stmt, UnOp};

/// A protocol state type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Ty {
    Bool,
    Int(IntTy),
}

/// A fixed-width integer type: its Rust name and its range.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct IntTy {
    name: &'static str,
    min: i128,
    max: i128,
}

/// Rust's type for an integer literal that nothing else types.
const I32: IntTy = IntTy::new("i32", i32::MIN as i128, i32::MAX as i128);

const INT_TYPES: [IntTy; 9] = [
    IntTy::new("u8", 0, u8::MAX as i128),
    IntTy::new("u16", 0, u16::MAX as i128),
    IntTy::new("u32", 0, u32::MAX as i128),
    IntTy::new("u64", 0, u64::MAX as i128),
    // The narrowest `usize` of a 32- or 64-bit target: a value beyond it is a
    // violation here even where a wider `usize` would hold it.
    IntTy::new("usize", 0, u32::MAX as i128),
    IntTy::new("i8", i8::MIN as i128, i8::MAX as i128),
    IntTy::new("i16", i16::MIN as i128, i16::MAX as i128),
    I32,
    IntTy::new("i64", i64::MIN as i128, i64::MAX as i128),
];

/// The name of every state type this translator reads.
#[cfg(test)]
pub(super) fn type_names() -> Vec<&'static str> {
    std::iter::once("bool")
        .chain(INT_TYPES.iter().map(|ty| ty.name))
        .collect()
}

impl IntTy {
    const fn new(name: &'static str, min: i128, max: i128) -> Self {
        Self { name, min, max }
    }

    fn named(name: &str) -> Option<Self> {
        INT_TYPES.iter().copied().find(|ty| ty.name == name)
    }

    fn range(self) -> String {
        format!("{}..{}", number(self.min), number(self.max))
    }
}

impl Ty {
    /// The type of a state field, from the macro's stringified Rust type.
    pub(super) fn parse(rust_type: &str) -> Option<Self> {
        match rust_type.trim() {
            "bool" => Some(Self::Bool),
            name => IntTy::named(name).map(Self::Int),
        }
    }

    /// The TLA+ set of the type's values.
    pub(super) fn domain(self) -> String {
        match self {
            Self::Bool => "BOOLEAN".to_string(),
            Self::Int(int) => int.range(),
        }
    }

    /// The type's zero: `false` or `0`.
    pub(super) fn zero(self) -> &'static str {
        match self {
            Self::Bool => "FALSE",
            Self::Int(_) => "0",
        }
    }

    /// The TLA+ text of a Rust value of this type; `None` for a value of
    /// another type, or out of this type's range.
    pub(super) fn value(self, value: ProtocolValue) -> Option<String> {
        match (self, value) {
            (Self::Bool, ProtocolValue::Bool(value)) => {
                Some(if value { "TRUE" } else { "FALSE" }.to_string())
            }
            (Self::Int(int), ProtocolValue::Int(value)) if int.min <= value && value <= int.max => {
                Some(number(value))
            }
            _ => None,
        }
    }

    fn describe(self) -> &'static str {
        match self {
            Self::Bool => "bool",
            Self::Int(int) => int.name,
        }
    }
}

/// A protocol's state variables: the field name (also its TLA+ name) and type.
pub(super) type Vars<'a> = [(&'a str, Ty)];

#[path = "rust_action.rs"]
mod body;
pub(super) use body::action;

/// A translated expression (see the module documentation).
struct Tla {
    value: String,
    defined: Option<String>,
}

impl Tla {
    fn total(value: String) -> Self {
        Self {
            value,
            defined: None,
        }
    }
}

/// Translate a `#[safety]` body: one `bool` expression. The result holds in a
/// state exactly when Rust evaluates the body to `true` there without
/// overflowing.
pub(super) fn invariant(body: &str, vars: &Vars) -> Result<String, String> {
    let stmts = statements(body)?;
    let [Stmt::Expr(expr, None)] = stmts.as_slice() else {
        return Err("a safety body must be exactly one `bool` expression".to_string());
    };
    let tla = translate(expr, Ty::Bool, vars)?;
    Ok(match tla.defined {
        Some(defined) => format!("({defined} /\\ {})", tla.value),
        None => tla.value,
    })
}

/// The TLA+ text of a `#[liveness]` body: exactly one `temporal!("...")` call.
pub(super) fn temporal(body: &str) -> Result<String, String> {
    let refusal = || "a liveness body must be exactly one `temporal!(\"<TLA+>\")` call".to_string();
    let block: syn::Block = syn::parse_str(body.trim()).map_err(|_| refusal())?;
    let mac = match block.stmts.as_slice() {
        [Stmt::Macro(stmt)] if stmt.semi_token.is_none() => &stmt.mac,
        [Stmt::Expr(Expr::Macro(expr), None)] => &expr.mac,
        _ => return Err(refusal()),
    };
    let path: Vec<String> = mac
        .path
        .segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect();
    let named = path == ["temporal"] && mac.path.leading_colon.is_none()
        || path == ["trust_vc", "temporal"];
    if !named {
        return Err(refusal());
    }
    let text: syn::LitStr = syn::parse2(mac.tokens.clone()).map_err(|_| refusal())?;
    let text = text.value();
    if text.trim().is_empty() {
        return Err(refusal());
    }
    Ok(text)
}

fn statements(body: &str) -> Result<Vec<Stmt>, String> {
    if body.contains('#') {
        return Err("an attribute or raw identifier (`#`) is not translated".to_string());
    }
    let body = body.trim();
    let block: syn::Block = syn::parse_str(body)
        .or_else(|_| syn::parse_str(&format!("{{ {body} }}")))
        .map_err(|error| format!("not a Rust block: {error}"))?;
    Ok(block.stmts)
}

/// `self.<field>` of a state variable: its name and type.
fn self_field<'a>(expr: &Expr, vars: &Vars<'a>) -> Result<(&'a str, Ty), String> {
    let refusal = || {
        format!(
            "`{}` is not a state field `self.<field>`",
            expr.to_token_stream()
        )
    };
    let Expr::Field(field) = expr else {
        return Err(refusal());
    };
    let (Expr::Path(base), Member::Named(name)) = (&*field.base, &field.member) else {
        return Err(refusal());
    };
    if base.qself.is_some() || !base.path.is_ident("self") {
        return Err(refusal());
    }
    vars.iter()
        .find(|(var, _)| name == var)
        .map(|&(var, ty)| (var, ty))
        .ok_or_else(|| format!("'{name}' is not a state variable of this protocol"))
}

fn translate(expr: &Expr, want: Ty, vars: &Vars) -> Result<Tla, String> {
    match expr {
        Expr::Paren(paren) => translate(&paren.expr, want, vars),
        Expr::Group(group) => translate(&group.expr, want, vars),
        Expr::Lit(lit) => literal(&lit.lit, want, false).map(Tla::total),
        Expr::Field(_) => {
            let (name, ty) = self_field(expr, vars)?;
            expect(ty, want, expr)?;
            Ok(Tla::total(name.to_string()))
        }
        Expr::Unary(unary) => match (unary.op, want) {
            (UnOp::Not(_), Ty::Bool) => {
                let inner = translate(&unary.expr, Ty::Bool, vars)?;
                Ok(Tla {
                    value: format!("(~{})", inner.value),
                    defined: inner.defined,
                })
            }
            (UnOp::Neg(_), Ty::Int(int)) if int.min < 0 => match &*unary.expr {
                Expr::Lit(lit) => literal(&lit.lit, want, true).map(Tla::total),
                operand => {
                    let inner = translate(operand, want, vars)?;
                    Ok(bounded(format!("(-{})", inner.value), inner.defined, int))
                }
            },
            _ => Err(format!(
                "`{}`: `!` is translated only on a `bool` and `-` only on a signed integer \
                 (`!` on an integer is bitwise NOT in Rust)",
                expr.to_token_stream()
            )),
        },
        Expr::Binary(binary) => translate_binary(binary, want, vars),
        _ => Err(format!("`{}` is not translated", expr.to_token_stream())),
    }
}

fn translate_binary(binary: &ExprBinary, want: Ty, vars: &Vars) -> Result<Tla, String> {
    let (left, right) = (&*binary.left, &*binary.right);
    let op = match binary.op {
        BinOp::And(_) | BinOp::Or(_) => {
            let is_and = matches!(binary.op, BinOp::And(_));
            expect(Ty::Bool, want, &Expr::Binary(binary.clone()))?;
            let l = translate(left, Ty::Bool, vars)?;
            let r = translate(right, Ty::Bool, vars)?;
            // The right operand runs only when the left does not decide.
            let r_defined = r.defined.map(|d| match is_and {
                true => format!("({} => {d})", l.value),
                false => format!("({} \\/ {d})", l.value),
            });
            let op = if is_and { "/\\" } else { "\\/" };
            return Ok(Tla {
                value: format!("({} {op} {})", l.value, r.value),
                defined: and(l.defined, r_defined),
            });
        }
        BinOp::Eq(_) => "=",
        BinOp::Ne(_) => "#",
        BinOp::Lt(_) => "<",
        BinOp::Le(_) => "<=",
        BinOp::Gt(_) => ">",
        BinOp::Ge(_) => ">=",
        BinOp::Add(_) => "+",
        BinOp::Sub(_) => "-",
        BinOp::Mul(_) => "*",
        other => {
            return Err(format!(
                "`{}` is not translated (its Rust meaning differs from any TLA+ operator \
                 this lane emits)",
                other.to_token_stream()
            ))
        }
    };
    if matches!(op, "+" | "-" | "*") {
        let Ty::Int(int) = want else {
            return Err(format!("`{}` is not a `bool`", binary.to_token_stream()));
        };
        let l = translate(left, want, vars)?;
        let r = translate(right, want, vars)?;
        let value = format!("({} {op} {})", l.value, r.value);
        return Ok(bounded(value, and(l.defined, r.defined), int));
    }
    expect(Ty::Bool, want, &Expr::Binary(binary.clone()))?;
    let operand = match (infer(left, vars)?, infer(right, vars)?) {
        (Some(l), Some(r)) if l != r => {
            return Err(format!(
                "`{}` compares a {} with a {}",
                binary.to_token_stream(),
                l.describe(),
                r.describe()
            ))
        }
        (Some(ty), _) | (_, Some(ty)) => ty,
        // Rust's fallback type for an integer literal.
        (None, None) => Ty::Int(I32),
    };
    if operand == Ty::Bool && !matches!(op, "=" | "#") {
        return Err(format!("`{}` orders `bool`s", binary.to_token_stream()));
    }
    let l = translate(left, operand, vars)?;
    let r = translate(right, operand, vars)?;
    Ok(Tla {
        value: format!("({} {op} {})", l.value, r.value),
        defined: and(l.defined, r.defined),
    })
}

/// The type an expression has on its own; `None` for an integer expression
/// built only from unsuffixed literals, which takes its type from context.
fn infer(expr: &Expr, vars: &Vars) -> Result<Option<Ty>, String> {
    Ok(match expr {
        Expr::Paren(paren) => infer(&paren.expr, vars)?,
        Expr::Group(group) => infer(&group.expr, vars)?,
        Expr::Lit(syn::ExprLit {
            lit: Lit::Bool(_), ..
        }) => Some(Ty::Bool),
        Expr::Lit(syn::ExprLit {
            lit: Lit::Int(int), ..
        }) if int.suffix().is_empty() => None,
        Expr::Lit(syn::ExprLit {
            lit: Lit::Int(int), ..
        }) => Some(Ty::parse(int.suffix()).ok_or_else(|| format!("`{int}` is not translated"))?),
        Expr::Field(_) => Some(self_field(expr, vars)?.1),
        Expr::Unary(unary) => infer(&unary.expr, vars)?,
        Expr::Binary(binary) => match binary.op {
            BinOp::Add(_) | BinOp::Sub(_) | BinOp::Mul(_) => {
                match (infer(&binary.left, vars)?, infer(&binary.right, vars)?) {
                    (Some(l), Some(r)) if l != r => {
                        return Err(format!("`{}` mixes types", binary.to_token_stream()))
                    }
                    (l, r) => l.or(r),
                }
            }
            _ => Some(Ty::Bool),
        },
        _ => return Err(format!("`{}` is not translated", expr.to_token_stream())),
    })
}

/// A literal of type `want`; `negated` for the operand of a unary `-`, which
/// Rust types together with its sign (`-128i8` is in range, `128i8` is not).
fn literal(lit: &Lit, want: Ty, negated: bool) -> Result<String, String> {
    match (lit, want) {
        (Lit::Bool(value), Ty::Bool) if !negated => {
            Ok(if value.value { "TRUE" } else { "FALSE" }.to_string())
        }
        (Lit::Int(int), Ty::Int(ty)) if int.suffix().is_empty() || int.suffix() == ty.name => {
            let magnitude: i128 = int
                .base10_parse()
                .map_err(|_| format!("`{int}` is out of range for {}", ty.name))?;
            let value = if negated { -magnitude } else { magnitude };
            if value < ty.min || value > ty.max {
                return Err(format!("`{int}` is out of range for {}", ty.name));
            }
            Ok(number(value))
        }
        _ => Err(format!(
            "`{}` is not a {} literal",
            lit.to_token_stream(),
            want.describe()
        )),
    }
}

fn expect(found: Ty, want: Ty, expr: &Expr) -> Result<(), String> {
    if found == want {
        return Ok(());
    }
    Err(format!(
        "`{}` is a {} where a {} is expected",
        expr.to_token_stream(),
        found.describe(),
        want.describe()
    ))
}

/// An arithmetic result: defined when its operands are and it fits `int`.
fn bounded(value: String, operands: Option<String>, int: IntTy) -> Tla {
    let fits = format!("({value} \\in {})", int.range());
    Tla {
        defined: and(operands, Some(fits)),
        value,
    }
}

fn and(left: Option<String>, right: Option<String>) -> Option<String> {
    match (left, right) {
        (Some(l), Some(r)) => Some(format!("({l} /\\ {r})")),
        (l, r) => l.or(r),
    }
}

fn number(value: i128) -> String {
    if value < 0 {
        format!("(-{})", value.unsigned_abs())
    } else {
        value.to_string()
    }
}
