//! A compact text rendering of VcIR, for reviews, dumps and test failures.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The format is for people, not for parsing back. Check sites are shown as
//! `[#n]` after the operator or statement that owns them; `as` is Verus's
//! clipping cast and `as=` an exact cast; `old(p)` is a parameter's entry
//! value.

use std::fmt::Write;

use crate::expr::{BinOp, CastKind, Expr, ExprKind, Lit, Place, Projection, QuantKind, UnOp};
use crate::item::{Body, Clause, FnDecl, FnRole, VcCrate};
use crate::stmt::{Block, ClauseAttrs, InvariantKind, Stmt, StmtKind};
use crate::ty::{IntRange, Ty};

/// Render a whole crate.
#[must_use]
pub fn crate_to_string(krate: &VcCrate) -> String {
    let mut out = String::new();
    for adt in &krate.adts {
        let _ = write!(out, "{:?} {}", adt.kind, adt.name);
        for variant in &adt.variants {
            let fields: Vec<String> = variant
                .fields
                .iter()
                .map(|f| format!("{}: {}", f.name, ty_name(krate, &f.ty)))
                .collect();
            let _ = write!(out, " {} {{ {} }}", variant.name, fields.join(", "));
        }
        out.push('\n');
    }
    for decl in &krate.fns {
        out.push_str(&fn_to_string(krate, decl));
    }
    for group in &krate.rec_groups {
        let members: Vec<String> = group
            .members
            .iter()
            .map(|(id, cycle)| {
                let name = krate.fn_decl(*id).map_or("?", |d| d.name.as_str());
                format!("{name} (cycle {cycle})")
            })
            .collect();
        let _ = writeln!(out, "recursive group: {}", members.join(", "));
    }
    out
}

/// Render one function.
#[must_use]
pub fn fn_to_string(krate: &VcCrate, decl: &FnDecl) -> String {
    let p = Printer { krate, decl };
    let mut out = String::new();
    let params: Vec<String> = decl
        .params
        .iter()
        .map(|id| p.local_decl(id.index()))
        .collect();
    let generics = if decl.type_params.is_empty() {
        String::new()
    } else {
        format!("<{}>", decl.type_params.join(", "))
    };
    let _ = writeln!(
        out,
        "{} fn {}{generics}({}) -> {}",
        decl.mode.name(),
        decl.name,
        params.join(", "),
        p.local_decl(decl.ret.index())
    );
    match decl.role {
        FnRole::Item => {}
        FnRole::TraitDecl => out.push_str("  #[trait-decl]\n"),
        FnRole::Instance => out.push_str("  #[instance]\n"),
        FnRole::Imported => out.push_str("  #[imported-declaration]\n"),
    }
    if decl.kind != crate::item::FnKind::Function {
        let _ = writeln!(out, "  #[declaration-kind={:?}]", decl.kind);
    }
    let attrs = &decl.attrs;
    if attrs.inline {
        out.push_str("  #[inline]\n");
    }
    if let Some(origin) = &attrs.instance {
        let _ = writeln!(
            out,
            "  #[instance-origin={:?} types={:?}]",
            origin.declaration, origin.type_args
        );
    }
    if attrs.opaque || attrs.external_body || attrs.rlimit.is_some() {
        let _ = writeln!(
            out,
            "  #[opaque={} external_body={} rlimit={:?}]",
            attrs.opaque, attrs.external_body, attrs.rlimit
        );
    }
    if attrs.exec_allows_no_decreases || attrs.is_decreases_by {
        let _ = writeln!(
            out,
            "  #[exec_allows_no_decreases={} decreases_by={}]",
            attrs.exec_allows_no_decreases, attrs.is_decreases_by
        );
    }
    for (word, clauses) in [
        ("requires", &decl.requires),
        ("ensures", &decl.ensures),
        ("recommends", &decl.recommends),
    ] {
        for clause in clauses {
            let _ = writeln!(out, "  {word} {}", p.clause(clause));
        }
    }
    if !decl.decreases.is_empty() {
        let _ = writeln!(out, "  decreases {}", p.exprs(&decl.decreases));
    }
    if let Some(when) = &decl.decreases_when {
        let _ = writeln!(out, "  when {}", p.expr(when));
    }
    if let Some(via) = decl.decreases_by {
        let name = krate.fn_decl(via).map_or("?", |d| d.name.as_str());
        let _ = writeln!(out, "  via {name}");
    }
    match &decl.body {
        Body::None => out.push_str("  (no body)\n"),
        Body::Spec(expr) => {
            let _ = writeln!(out, "  = {}", p.expr(expr));
        }
        Body::Stmts(block) => p.block(block, 1, &mut out),
        Body::Constant(expr) => {
            let _ = writeln!(out, "  (initializer {})", p.expr(expr));
        }
    }
    out
}

struct Printer<'a> {
    krate: &'a VcCrate,
    decl: &'a FnDecl,
}

impl Printer<'_> {
    fn local_name(&self, index: usize) -> String {
        self.decl
            .locals
            .get(index)
            .map_or_else(|| format!("?{index}"), |l| l.name.clone())
    }

    fn local_decl(&self, index: usize) -> String {
        match self.decl.locals.get(index) {
            Some(l) => format!(
                "{}{}: {} {}",
                if l.mutable { "mut " } else { "" },
                l.name,
                l.mode.name(),
                ty_name(self.krate, &l.ty)
            ),
            None => format!("?{index}"),
        }
    }

    fn clause(&self, clause: &Clause) -> String {
        format!("{}{}", self.expr(&clause.expr), attrs_suffix(&clause.attrs))
    }

    fn place(&self, place: &Place) -> String {
        let mut s = self.local_name(place.local.index());
        for projection in &place.projections {
            s = match projection {
                Projection::Deref => format!("(*{s})"),
                Projection::Field { variant, field } => format!("{s}.{variant}:{field}"),
                Projection::TupleField(index) => format!("{s}.{index}"),
            };
        }
        s
    }

    fn fn_name(&self, id: crate::ids::FnId) -> String {
        self.krate
            .fn_decl(id)
            .map_or_else(|| format!("{id:?}"), |f| f.name.clone())
    }

    fn expr(&self, e: &Expr) -> String {
        match &e.kind {
            ExprKind::IntegerConstant(value) => format!("{value:?}"),
            ExprKind::Lit(Lit::Bool(b)) => b.to_string(),
            ExprKind::Lit(Lit::Unit) => "()".to_string(),
            ExprKind::Lit(Lit::Int(lit)) => format!(
                "{}{}{}",
                if lit.negative { "-" } else { "" },
                lit.magnitude,
                ty_name(self.krate, &e.ty)
            ),
            ExprKind::Read(place) => self.place(place),
            ExprKind::Old(place) => format!("old({})", self.place(place)),
            ExprKind::Unary { op, arg, check } => {
                let op = match op {
                    UnOp::Not => "!",
                    UnOp::Neg => "-",
                };
                format!("{op}{}{}", site(*check), self.expr(arg))
            }
            ExprKind::Binary {
                op,
                lhs,
                rhs,
                check,
            } => format!(
                "({} {}{} {})",
                self.expr(lhs),
                bin_op(*op),
                site(*check),
                self.expr(rhs)
            ),
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => format!(
                "(if {} then {} else {})",
                self.expr(cond),
                self.expr(then_expr),
                self.expr(else_expr)
            ),
            ExprKind::Let { local, value, body } => format!(
                "(let {} = {} in {})",
                self.local_name(local.index()),
                self.expr(value),
                self.expr(body)
            ),
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => {
                format!(
                    "{}{}({})",
                    self.fn_name(*callee),
                    self.type_args(type_args),
                    self.exprs(args)
                )
            }
            ExprKind::Cast { arg, kind } => {
                let word = match kind {
                    CastKind::Exact => "as=",
                    CastKind::As => "as",
                };
                format!("({} {word} {})", self.expr(arg), ty_name(self.krate, &e.ty))
            }
            ExprKind::Ctor {
                variant, fields, ..
            } => format!(
                "{}#{variant}{{{}}}",
                ty_name(self.krate, &e.ty),
                self.exprs(fields)
            ),
            ExprKind::IsVariant { base, variant } => {
                format!("({} is #{variant})", self.expr(base))
            }
            ExprKind::Tuple(elems) => {
                let comma = if elems.len() == 1 { "," } else { "" };
                format!("({}{comma})", self.exprs(elems))
            }
            ExprKind::Field {
                base,
                variant,
                field,
            } => format!("{}.{variant}:{field}", self.expr(base)),
            ExprKind::TupleField { base, index } => format!("{}.{index}", self.expr(base)),
            ExprKind::Borrow(inner) => format!("&{}", self.expr(inner)),
            ExprKind::ProofInSpec(block) => {
                let mut inner = String::new();
                self.block(block, 0, &mut inner);
                let stmts: Vec<&str> = inner.lines().map(str::trim).collect();
                format!("proof {{ {} }}", stmts.join("; "))
            }
            ExprKind::Quant {
                kind,
                vars,
                triggers,
                body,
            } => {
                let word = match kind {
                    QuantKind::Forall => "forall",
                    QuantKind::Exists => "exists",
                };
                format!(
                    "({word}|{}| {}{})",
                    self.binders(vars),
                    self.triggers(triggers),
                    self.expr(body)
                )
            }
            ExprKind::Choose {
                vars,
                triggers,
                cond,
                result,
            } => format!(
                "(choose|{}| {}{} => {})",
                self.binders(vars),
                self.triggers(triggers),
                self.expr(cond),
                self.expr(result)
            ),
            ExprKind::UntriggeredQuant {
                kind,
                vars,
                trigger_candidates,
                body,
            } => format!(
                "(untriggered-{kind:?}|{}| candidates [{}] {})",
                self.binders(vars),
                self.exprs(trigger_candidates),
                self.expr(body)
            ),
            ExprKind::UntriggeredChoose {
                vars,
                trigger_candidates,
                cond,
                result,
            } => format!(
                "(untriggered-choose|{}| candidates [{}] {} => {})",
                self.binders(vars),
                self.exprs(trigger_candidates),
                self.expr(cond),
                self.expr(result)
            ),
        }
    }

    fn binders(&self, vars: &[(crate::ids::LocalId, Ty)]) -> String {
        vars.iter()
            .map(|(var, _)| self.local_decl(var.index()))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn triggers(&self, triggers: &[Vec<Expr>]) -> String {
        triggers
            .iter()
            .map(|group| format!("#![trigger {}] ", self.exprs(group)))
            .collect()
    }

    fn type_args(&self, args: &[Ty]) -> String {
        if args.is_empty() {
            return String::new();
        }
        let names: Vec<String> = args.iter().map(|t| ty_name(self.krate, t)).collect();
        format!("::<{}>", names.join(", "))
    }

    fn exprs(&self, es: &[Expr]) -> String {
        es.iter()
            .map(|e| self.expr(e))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn block(&self, block: &Block, depth: usize, out: &mut String) {
        for stmt in &block.stmts {
            self.stmt(stmt, depth, out);
        }
    }

    fn stmt(&self, stmt: &Stmt, depth: usize, out: &mut String) {
        let pad = "  ".repeat(depth);
        match &stmt.kind {
            StmtKind::Let { local, init } => {
                let _ = write!(out, "{pad}let {}", self.local_decl(local.index()));
                if let Some(init) = init {
                    let _ = write!(out, " = {}", self.expr(init));
                }
                out.push('\n');
            }
            StmtKind::Assign { place, value } => {
                let _ = writeln!(out, "{pad}{} := {}", self.place(place), self.expr(value));
            }
            StmtKind::Call {
                callee,
                type_args,
                args,
                dest,
                site: s,
            } => {
                let dest = dest
                    .as_ref()
                    .map_or(String::new(), |d| format!("{} := ", self.place(d)));
                let _ = writeln!(
                    out,
                    "{pad}{dest}call[#{}] {}{}({})",
                    s.0,
                    self.fn_name(*callee),
                    self.type_args(type_args),
                    self.exprs(args)
                );
            }
            StmtKind::Assert {
                expr,
                site: s,
                attrs,
            } => {
                let _ = writeln!(
                    out,
                    "{pad}assert[#{}] {}{}",
                    s.0,
                    self.expr(expr),
                    attrs_suffix(attrs)
                );
            }
            StmtKind::Assume { expr, attrs } => {
                let _ = writeln!(
                    out,
                    "{pad}assume {}{}",
                    self.expr(expr),
                    attrs_suffix(attrs)
                );
            }
            StmtKind::AssertBitVector {
                requires,
                ensures,
                architecture,
                site,
            } => {
                let _ = writeln!(
                    out,
                    "{pad}assert_bitvector[#{}] {architecture:?} {{",
                    site.0
                );
                for (kind, clauses) in [("requires", requires), ("ensures", ensures)] {
                    for clause in clauses {
                        let _ = writeln!(
                            out,
                            "{pad}  {kind} {}{}",
                            self.expr(&clause.expr),
                            attrs_suffix(&clause.attrs)
                        );
                    }
                }
                let _ = writeln!(out, "{pad}}}");
            }
            StmtKind::If {
                cond,
                then_block,
                else_block,
            } => {
                let _ = writeln!(out, "{pad}if {} {{", self.expr(cond));
                self.block(then_block, depth + 1, out);
                let _ = writeln!(out, "{pad}}} else {{");
                self.block(else_block, depth + 1, out);
                let _ = writeln!(out, "{pad}}}");
            }
            StmtKind::Return { value, site: s } => {
                let value = value
                    .as_ref()
                    .map_or(String::new(), |v| format!(" {}", self.expr(v)));
                let _ = writeln!(out, "{pad}return[#{}]{value}", s.0);
            }
            StmtKind::Reveal { callee, fuel } => {
                let _ = writeln!(out, "{pad}reveal {} fuel={fuel:?}", self.fn_name(*callee));
            }
            StmtKind::Hide { callee } => {
                let _ = writeln!(out, "{pad}hide {}", self.fn_name(*callee));
            }
            StmtKind::Ghost(block) => {
                let _ = writeln!(out, "{pad}ghost {{");
                self.block(block, depth + 1, out);
                let _ = writeln!(out, "{pad}}}");
            }
            StmtKind::Block(block) => {
                let _ = writeln!(out, "{pad}{{");
                self.block(block, depth + 1, out);
                let _ = writeln!(out, "{pad}}}");
            }
            StmtKind::Loop(lp) => {
                let isolation = if lp.isolation { "" } else { " no-isolation" };
                let complex = if lp.allow_complex_invariants {
                    " complex"
                } else {
                    ""
                };
                let _ = writeln!(
                    out,
                    "{pad}loop#{}[#{} #{} #{}]{isolation}{complex} {{",
                    lp.id.0, lp.sites.entry.0, lp.sites.end.0, lp.sites.exit.0
                );
                let inner = "  ".repeat(depth + 1);
                if let Some(cond) = &lp.cond {
                    let _ = writeln!(out, "{inner}while {{");
                    self.block(&cond.block, depth + 2, out);
                    let _ = writeln!(out, "{inner}}} {}", self.expr(&cond.expr));
                }
                for inv in &lp.invariants {
                    let kind = match inv.kind {
                        InvariantKind::ExceptBreak => "invariant_except_break",
                        InvariantKind::Always => "invariant",
                        InvariantKind::Ensures => "ensures",
                    };
                    let _ = writeln!(out, "{inner}{kind} {}", self.expr(&inv.expr));
                }
                if !lp.decreases.is_empty() {
                    let _ = writeln!(out, "{inner}decreases {}", self.exprs(&lp.decreases));
                }
                let _ = writeln!(out, "{inner}do {{");
                self.block(&lp.body, depth + 2, out);
                let _ = writeln!(out, "{inner}}}");
                let _ = writeln!(out, "{pad}}}");
            }
            StmtKind::Break { target, site: s } => {
                let _ = writeln!(out, "{pad}break[#{}] loop#{}", s.0, target.0);
            }
            StmtKind::Continue { target, site: s } => {
                let _ = writeln!(out, "{pad}continue[#{}] loop#{}", s.0, target.0);
            }
            StmtKind::Unreachable => {
                let _ = writeln!(out, "{pad}unreachable");
            }
        }
    }
}

fn site(check: Option<crate::ids::SiteId>) -> String {
    check.map_or(String::new(), |s| format!("[#{}]", s.0))
}

fn attrs_suffix(attrs: &ClauseAttrs) -> String {
    let mut s = String::new();
    for note in &attrs.proof_notes {
        let _ = write!(s, " @note({note:?})");
    }
    for err in &attrs.custom_errs {
        let _ = write!(s, " @custom_err({err:?})");
    }
    s
}

fn bin_op(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::Implies => "==>",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
    }
}

/// The name of a type.
#[must_use]
pub fn ty_name(krate: &VcCrate, ty: &Ty) -> String {
    match ty {
        Ty::Bool => "bool".to_string(),
        Ty::Unit => "()".to_string(),
        Ty::Int(range) => match range {
            IntRange::Int => "int".to_string(),
            IntRange::Nat => "nat".to_string(),
            IntRange::U(bits) => format!("u{bits}"),
            IntRange::I(bits) => format!("i{bits}"),
            IntRange::USize => "usize".to_string(),
            IntRange::ISize => "isize".to_string(),
            IntRange::Char => "char".to_string(),
        },
        Ty::Tuple(elems) => format!(
            "({}{})",
            elems
                .iter()
                .map(|t| ty_name(krate, t))
                .collect::<Vec<_>>()
                .join(", "),
            if elems.len() == 1 { "," } else { "" }
        ),
        Ty::Adt(id, args) => {
            let name = krate
                .adt(*id)
                .map_or_else(|| format!("{id:?}"), |a| a.name.clone());
            if args.is_empty() {
                name
            } else {
                let args: Vec<String> = args.iter().map(|t| ty_name(krate, t)).collect();
                format!("{name}<{}>", args.join(", "))
            }
        }
        Ty::Ref { mutable, inner } => format!(
            "&{}{}",
            if *mutable { "mut " } else { "" },
            ty_name(krate, inner)
        ),
        Ty::Param(n) => format!("T{n}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ids::{DefHash, FnId, LocalId, SiteId, SpanId};
    use crate::item::{FnAttrs, LocalDecl, LocalKind, Mode};

    #[test]
    fn renders_a_checked_exec_function() {
        let local = |name: &str, ty: Ty, kind| LocalDecl {
            name: name.to_string(),
            ty,
            mode: Mode::Exec,
            mutable: false,
            kind,
            span: SpanId(0),
        };
        let read = |i| Expr::read(Place::local(LocalId(i)), Ty::uint(64), SpanId(0));
        let sum = Expr::checked_binary(
            BinOp::Add,
            read(1),
            read(2),
            Ty::uint(64),
            SiteId(1),
            SpanId(0),
        );
        let decl = FnDecl {
            id: FnId(DefHash::new(0, 1)),
            name: "example".to_string(),
            span: SpanId(0),
            mode: Mode::Exec,
            role: FnRole::Item,
            kind: Default::default(),
            type_params: Vec::new(),
            locals: vec![
                local("z", Ty::uint(64), LocalKind::Return),
                local("x", Ty::uint(64), LocalKind::Param),
                local("y", Ty::uint(64), LocalKind::Param),
            ],
            params: vec![LocalId(1), LocalId(2)],
            ret: LocalId(0),
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: Vec::new(),
            decreases_when: None,
            decreases_by: None,
            attrs: FnAttrs::default(),
            body: Body::Stmts(Block::new(vec![Stmt::new(
                SpanId(0),
                StmtKind::Return {
                    value: Some(sum),
                    site: SiteId(2),
                },
            )])),
        };
        let mut krate = VcCrate::new("t");
        krate.fns.push(decl);
        assert_eq!(
            crate_to_string(&krate),
            "exec fn example(x: exec u64, y: exec u64) -> z: exec u64\n  return[#2] (x +[#1] y)\n"
        );
    }
}
