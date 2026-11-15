//! The type Rust infers for a binding whose initializer is an UNSUFFIXED
//! integer literal form (`let mut i = 0`, `let mut w = if c { 0 } else { 1 }`).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Rust gives such a binding ONE type, unified from all of its uses, and falls
//! back to `i32` only when no use fixes one. The extractor substitutes the
//! literal form wherever the binding is read, and a peer types it there; but a
//! loop that writes the binding needs the binding's type to declare its
//! loop-head value at, before the loop's uses are seen. Guessing `i32` there
//! made `let mut w = 0; while .. { w = 200; } let z = w + y;` (`y: u8`) a
//! mixed `i32 + u8`, hence EXACT, addition: its overflow was missed.
//!
//! [`infer_untyped_binding_type`] reads the statements after the `let`:
//!
//! * a use that unifies the binding with an operand of a known type — an
//!   arithmetic, bitwise or comparison operator, an assignment or compound
//!   assignment, a `let z: T = w` — fixes that type. In a program the compiler
//!   accepts, every such use agrees, so the first one found is the type;
//! * when no use outside a macro fixes one, the binding is `i32` only if every
//!   use is one this reading understands and fixes nothing (an operand next to
//!   an unsuffixed literal, a shift, a cast, a comparison method's receiver, …); a
//!   use inside a macro next to a typed operand may or may not reach the type
//!   checker, so it decides nothing;
//! * anything else — an unread use, a rebinding of the name or of a peer's
//!   name after the `let` — is unknown (`None`), and the caller fails closed.
//!   An operation that has the binding's type (`w - 1`, `w >> 1`, `-w`) is a
//!   use of the binding wherever it stands: next to an operand of a unifying
//!   operator that operand types it, and in any position this reading does not
//!   type (a call or method argument, a struct field, a tail, …) it is
//!   unknown, as the bare name there is. A `let z = w - 1;` without an
//!   ascription is read through the uses of `z` (`untyped_binding_copy.rs`).

use crate::ir::TrustVcType;
use syn::visit::Visit;
use syn::{BinOp, Expr, Stmt};

/// What one use of the binding says about its type.
#[derive(Debug, Clone, PartialEq)]
enum Constraint {
    /// The use unifies the binding with a value of this type.
    Fixed(TrustVcType),
    /// The use is understood and fixes nothing.
    Free,
    /// The use is not understood.
    Unknown,
}

/// What the reading of a binding's uses knows of the names and callees at
/// its `let`.
pub(super) struct UseTypes<'n> {
    /// The type of a name visible at the `let`.
    pub(super) peer: &'n dyn Fn(&str) -> Option<TrustVcType>,
    /// The fixed-width integer type of parameter `index` of the callee of a
    /// call, when this lane reads it (a file function's declared parameter).
    pub(super) call_param: &'n dyn Fn(&syn::ExprCall, usize) -> Option<TrustVcType>,
}

/// The type Rust infers for the binding `name`, bound by an unascribed `let`
/// to an unsuffixed integer literal form and used in `rest` (the statements
/// after it in its block), or `None` when that is not determined here.
pub(super) fn infer_untyped_binding_type(
    name: &str,
    rest: &[Stmt],
    types: &UseTypes<'_>,
) -> Option<TrustVcType> {
    match binding_constraint(name, rest, types) {
        Constraint::Fixed(ty) => Some(ty),
        Constraint::Free => Some(TrustVcType::Int { width: 32 }),
        Constraint::Unknown => None,
    }
}

/// Every name a pattern or closure parameter binds.
struct Rebound {
    names: std::collections::BTreeSet<String>,
}

impl<'ast> Visit<'ast> for Rebound {
    fn visit_pat_ident(&mut self, ident: &'ast syn::PatIdent) {
        self.names.insert(ident.ident.to_string());
        syn::visit::visit_pat_ident(self, ident);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        for expr in macro_exprs(mac).iter().flatten() {
            self.visit_expr(expr);
        }
    }
}

struct Uses<'n> {
    name: &'n str,
    /// How the binding is read through `name` ([`Reading`]).
    reading: Reading,
    rebound: &'n std::collections::BTreeSet<String>,
    types: &'n UseTypes<'n>,
    in_macro: bool,
    /// Set by a caller of `visit_expr` whose position types the expression
    /// it visits (see `visit_expr`); consumed by that call.
    typed_position: bool,
    fixed: Vec<TrustVcType>,
    macro_fixed: bool,
    unknown: bool,
}

impl Uses<'_> {
    fn is_name(&self, expr: &Expr) -> bool {
        let names = |expr: &Expr| path_ident(peel(expr)).is_some_and(|ident| ident == self.name);
        match (self.reading, peel(expr)) {
            (Reading::Name, expr) => names(expr),
            (Reading::Deref, Expr::Unary(unary)) if matches!(unary.op, syn::UnOp::Deref(_)) => {
                names(&unary.expr)
            }
            (Reading::Element, Expr::Index(index)) => names(&index.expr),
            _ => false,
        }
    }

    /// Whether `expr` has the binding's type because it is the binding or an
    /// operation over it that keeps its operand's type: an arithmetic or
    /// bitwise operation with the binding on either side, a shift with the
    /// binding on its left (a shift's value has its left operand's type), a
    /// negation or a bitwise `!` of one.
    fn carries_name(&self, expr: &Expr) -> bool {
        match peel(expr) {
            expr if self.is_name(expr) => true,
            // A compound assignment's value is `()`.
            Expr::Binary(binary) if is_compound_assignment(&binary.op) => false,
            Expr::Binary(binary) if is_shift(&binary.op) => self.carries_name(&binary.left),
            Expr::Binary(binary) if unifying_operator(&binary.op) && !is_comparison(&binary.op) => {
                self.carries_name(&binary.left) || self.carries_name(&binary.right)
            }
            Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_) | syn::UnOp::Not(_)) => {
                self.carries_name(&unary.expr)
            }
            // `w.max(1)`, `w.clone()`: a trait method whose result has its
            // receiver's type.
            Expr::MethodCall(call) => {
                method_typing(call).returns_self() && self.carries_name(&call.receiver)
            }
            _ => false,
        }
    }

    /// Visit `expr`, which stands where its type is accounted for: an operand
    /// of a unifying operator whose peer was recorded, either side of a shift
    /// (a shift's value has its left operand's type, which the shift's own
    /// position types; its amount is typed apart), a cast operand, a method
    /// receiver, the value written to the binding itself, or the value of an
    /// ascribed `let`.
    fn visit_typed(&mut self, expr: &Expr) {
        self.typed_position = true;
        self.visit_expr(expr);
        self.typed_position = false;
    }

    fn record(&mut self, constraint: Constraint) {
        match constraint {
            Constraint::Fixed(_) if self.in_macro => self.macro_fixed = true,
            Constraint::Fixed(ty) => self.fixed.push(ty),
            Constraint::Free => {}
            Constraint::Unknown => self.unknown = true,
        }
    }

    /// The type an operand unified with the binding has.
    fn operand(&self, expr: &Expr) -> Constraint {
        let expr = peel(expr);
        if self.is_name(expr) {
            return Constraint::Free;
        }
        if super::body_extract::expr_is_default_int_literal_value(expr) {
            return Constraint::Free;
        }
        match expr {
            Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Int(lit),
                ..
            }) => match TrustVcType::parse_or_opaque(lit.suffix()) {
                ty if crate::ir_lowering::is_fixed_width_int(&ty) => Constraint::Fixed(ty),
                _ => Constraint::Unknown,
            },
            Expr::Cast(cast) => {
                let spelled = quote::ToTokens::to_token_stream(&*cast.ty).to_string();
                match TrustVcType::parse_or_opaque(&spelled) {
                    ty if crate::ir_lowering::is_fixed_width_int(&ty) => Constraint::Fixed(ty),
                    _ => Constraint::Unknown,
                }
            }
            Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_)) => {
                self.operand(&unary.expr)
            }
            // `w.max(y)` next to a peer: the call has the binding's type, and
            // its own arguments are recorded where it is visited.
            Expr::MethodCall(_) if self.carries_name(expr) => Constraint::Free,
            Expr::Binary(binary) if unifying_operator(&binary.op) && !is_comparison(&binary.op) => {
                match (self.operand(&binary.left), self.operand(&binary.right)) {
                    (Constraint::Unknown, _) | (_, Constraint::Unknown) => Constraint::Unknown,
                    (Constraint::Fixed(left), Constraint::Fixed(right)) if left != right => {
                        Constraint::Unknown
                    }
                    (Constraint::Fixed(ty), _) | (_, Constraint::Fixed(ty)) => {
                        Constraint::Fixed(ty)
                    }
                    (Constraint::Free, Constraint::Free) => Constraint::Free,
                }
            }
            other => match path_ident(other) {
                Some(ident) if !self.rebound.contains(&ident) => match (self.types.peer)(&ident) {
                    Some(ty) if crate::ir_lowering::is_integer_type(&ty) => Constraint::Fixed(ty),
                    _ => Constraint::Unknown,
                },
                _ => Constraint::Unknown,
            },
        }
    }
}

impl<'ast> Visit<'ast> for Uses<'_> {
    fn visit_block(&mut self, block: &'ast syn::Block) {
        self.visit_stmts(&block.stmts);
    }

    fn visit_expr(&mut self, expr: &'ast Expr) {
        // An operation of the binding's type (`w - 1`) standing where this
        // reading does not type it — `g(w - 1)`, `S { g: w - 1 }`,
        // `v.push(w - 1)`, a tail, `let z = w - 1;` — is typed by a use not
        // read here, exactly as the bare name there would be. Read as a use
        // that fixes nothing, it left a loop-written `let mut w = 0` at `i32`
        // where `g8(w - 45)` makes it a `u8`, and the loop's `u8` overflow
        // unchecked.
        let typed = std::mem::replace(&mut self.typed_position, false);
        if !typed && !self.is_name(expr) && self.carries_name(expr) {
            self.record(Constraint::Unknown);
        }
        match expr {
            Expr::Binary(binary) if is_shift(&binary.op) => {
                // A shift's amount and its value are typed independently; the
                // VALUE has its left operand's type, so a peer the shift meets
                // (`(w >> 1) + y`) types the binding: recorded where the shift
                // is an operand below (`carries_name`).
                for side in [&binary.left, &binary.right] {
                    if !self.is_name(side) {
                        self.visit_typed(side);
                    }
                }
            }
            Expr::Binary(binary) if unifying_operator(&binary.op) => {
                // The binding reaches this operation THROUGH an operation of its
                // own type (`w - 1 + y`, `(w >> 1) < y`): the other operand
                // types it as a direct peer would. Missed, `let z = w - 1 + y;`
                // left a loop-written `w` at `i32` and the loop's `u8`
                // overflow unchecked.
                let left_carries = !self.is_name(&binary.left) && self.carries_name(&binary.left);
                let right_carries =
                    !self.is_name(&binary.right) && self.carries_name(&binary.right);
                if left_carries || right_carries {
                    let constraint = match (
                        self.carries_name(&binary.left),
                        self.carries_name(&binary.right),
                    ) {
                        (true, true) => Constraint::Free,
                        (true, false) => self.operand(&binary.right),
                        _ => self.operand(&binary.left),
                    };
                    self.record(constraint);
                }
                if self.is_name(&binary.left) {
                    let constraint = self.operand(&binary.right);
                    self.record(constraint);
                } else if left_carries {
                    self.visit_typed(&binary.left);
                } else {
                    self.visit_expr(&binary.left);
                }
                if self.is_name(&binary.right) {
                    let constraint = self.operand(&binary.left);
                    self.record(constraint);
                } else if right_carries {
                    self.visit_typed(&binary.right);
                } else {
                    self.visit_expr(&binary.right);
                }
            }
            Expr::Assign(assign) if self.is_name(&assign.left) => {
                let constraint = self.operand(&assign.right);
                self.record(constraint);
                self.visit_typed(&assign.right);
            }
            // `z = w - 1`: the place's type types the operation.
            Expr::Assign(assign) if self.carries_name(&assign.right) => {
                let constraint = self.operand(&assign.left);
                self.record(constraint);
                self.visit_expr(&assign.left);
                if !self.is_name(&assign.right) {
                    self.visit_typed(&assign.right);
                }
            }
            // `g8(w)`, `g8(w - 45)`: a parameter this lane reads types it.
            Expr::Call(call) if self.visit_typed_call(call) => {}
            Expr::Cast(cast) if self.is_name(&cast.expr) => {}
            // A cast's operand is typed apart from its target.
            Expr::Cast(cast) if self.carries_name(&cast.expr) => self.visit_typed(&cast.expr),
            // A method called on the binding (or on an operation of its type),
            // or one whose argument is: `method::MethodTyping`.
            Expr::MethodCall(call) if self.carries_name(&call.receiver) => {
                self.visit_receiver_method_call(call);
            }
            Expr::MethodCall(call) if self.method_argument_carries_name(call) => {
                self.visit_argument_method_call(call);
            }
            // A negation or `!` passes its operand's type to its own position,
            // which was checked above.
            Expr::Unary(unary)
                if matches!(unary.op, syn::UnOp::Neg(_) | syn::UnOp::Not(_))
                    && self.carries_name(&unary.expr) =>
            {
                if !self.is_name(&unary.expr) {
                    self.visit_typed(&unary.expr);
                }
            }
            Expr::Paren(paren) => {
                self.typed_position = typed;
                self.visit_expr(&paren.expr);
            }
            Expr::Group(group) => {
                self.typed_position = typed;
                self.visit_expr(&group.expr);
            }
            // `a.len()` of an array read by its elements reads no element.
            Expr::MethodCall(call) if self.is_length_read(call) => {}
            other if self.is_name(other) || self.is_bare_holder(other) => {
                self.record(Constraint::Unknown)
            }
            other => syn::visit::visit_expr(self, other),
        }
    }

    fn visit_local(&mut self, local: &'ast syn::Local) {
        if let (syn::Pat::Type(pat_type), Some(init)) = (&local.pat, &local.init) {
            if self.carries_name(&init.expr) && !self.is_name(&init.expr) {
                // `let z: u8 = w - 1;`: the ascription types the operation,
                // hence the binding; its operands are still read below.
                let spelled = quote::ToTokens::to_token_stream(&*pat_type.ty).to_string();
                let ty = TrustVcType::parse_or_opaque(&spelled);
                self.record(if crate::ir_lowering::is_fixed_width_int(&ty) {
                    Constraint::Fixed(ty)
                } else {
                    Constraint::Unknown
                });
                self.visit_pat(&local.pat);
                self.visit_typed(&init.expr);
                if let Some((_, diverge)) = &init.diverge {
                    self.visit_expr(diverge);
                }
                return;
            }
            if self.is_name(&init.expr) && init.diverge.is_none() {
                let spelled = quote::ToTokens::to_token_stream(&*pat_type.ty).to_string();
                let ty = TrustVcType::parse_or_opaque(&spelled);
                self.record(if crate::ir_lowering::is_fixed_width_int(&ty) {
                    Constraint::Fixed(ty)
                } else {
                    Constraint::Unknown
                });
                return;
            }
        }
        syn::visit::visit_local(self, local);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        match macro_exprs(mac) {
            Some(exprs) => {
                let outer = std::mem::replace(&mut self.in_macro, true);
                for expr in &exprs {
                    self.visit_expr(expr);
                }
                self.in_macro = outer;
            }
            None => {
                if tokens_mention(mac.tokens.clone(), self.name) {
                    self.unknown = true;
                }
            }
        }
    }
}

/// The comma-separated expressions of a macro invocation, or `None` when its
/// tokens are not such a list.
fn macro_exprs(mac: &syn::Macro) -> Option<Vec<Expr>> {
    mac.parse_body_with(syn::punctuated::Punctuated::<Expr, syn::Token![,]>::parse_terminated)
        .ok()
        .map(|exprs| exprs.into_iter().collect())
}

fn tokens_mention(tokens: proc_macro2::TokenStream, name: &str) -> bool {
    tokens.into_iter().any(|tree| match tree {
        proc_macro2::TokenTree::Ident(ident) => ident == name,
        proc_macro2::TokenTree::Group(group) => tokens_mention(group.stream(), name),
        _ => false,
    })
}

fn peel(expr: &Expr) -> &Expr {
    match expr {
        Expr::Paren(paren) => peel(&paren.expr),
        Expr::Group(group) => peel(&group.expr),
        other => other,
    }
}

fn path_ident(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(path) if path.qself.is_none() => path.path.get_ident().map(ToString::to_string),
        _ => None,
    }
}

/// An operator whose two integer operands have one type: arithmetic,
/// bitwise, comparison, and their compound assignments (not the shifts).
fn unifying_operator(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::Add(_)
            | BinOp::Sub(_)
            | BinOp::Mul(_)
            | BinOp::Div(_)
            | BinOp::Rem(_)
            | BinOp::BitAnd(_)
            | BinOp::BitOr(_)
            | BinOp::BitXor(_)
            | BinOp::AddAssign(_)
            | BinOp::SubAssign(_)
            | BinOp::MulAssign(_)
            | BinOp::DivAssign(_)
            | BinOp::RemAssign(_)
            | BinOp::BitAndAssign(_)
            | BinOp::BitOrAssign(_)
            | BinOp::BitXorAssign(_)
    ) || is_comparison(op)
}

fn is_comparison(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq(_) | BinOp::Ne(_) | BinOp::Lt(_) | BinOp::Le(_) | BinOp::Gt(_) | BinOp::Ge(_)
    )
}

fn is_compound_assignment(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::AddAssign(_)
            | BinOp::SubAssign(_)
            | BinOp::MulAssign(_)
            | BinOp::DivAssign(_)
            | BinOp::RemAssign(_)
            | BinOp::BitAndAssign(_)
            | BinOp::BitOrAssign(_)
            | BinOp::BitXorAssign(_)
            | BinOp::ShlAssign(_)
            | BinOp::ShrAssign(_)
    )
}

fn is_shift(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::Shl(_) | BinOp::Shr(_) | BinOp::ShlAssign(_) | BinOp::ShrAssign(_)
    )
}

#[path = "untyped_binding_call.rs"]
mod call;
#[path = "untyped_binding_scope.rs"]
mod scope;
pub(super) use scope::infer_untyped_element_type;
use scope::Reading;
use scope::{pattern_binds, PatternRebound};
#[path = "untyped_binding_copy.rs"]
mod copy;
use copy::binding_constraint;
#[path = "untyped_binding_method.rs"]
mod method;
use method::method_typing;

#[cfg(test)]
#[path = "untyped_binding_type_tests.rs"]
mod tests;
