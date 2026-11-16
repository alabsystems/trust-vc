//! The VC generator on hand-built VcIR, answered by trust-vc-core.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Each test builds a small crate in the shape the reader produces for
//! upstream Verus programs, generates its checks and solves them. Every
//! positive case has a liar twin that differs in one place and must not be
//! proved. Needs the `solve` feature.

use trust_vc_vcir::solve::{check, Limits, Verdict};
use trust_vc_vcir::vcgen::{generate, Check, CheckKind, FnVcs, InvariantAt, QueryGroup};
use trust_vc_vcir::{
    check_crate, AdtDecl, AdtId, AdtKind, BinOp, Block, Body, CastKind, Clause, ClauseAttrs,
    DefHash, DefOrder, Expr, ExprKind, FieldDecl, FnAttrs, FnDecl, FnId, FnRole, InvariantKind,
    LocalDecl, LocalId, LocalKind, Loop, LoopCond, LoopId, LoopInvariant, LoopSites, Mode, Place,
    Projection, QuantKind, RecGroup, SiteId, SpanId, Stmt, StmtKind, Ty, VariantDecl, VcCrate,
    WfClass,
};

#[path = "broadcast_contracts/mod.rs"]
mod broadcast_contracts;

#[path = "reveal_scopes/mod.rs"]
mod reveal_scopes;

#[path = "constants/mod.rs"]
mod constants;

// ----------------------------------------------------------------------
// Builders
// ----------------------------------------------------------------------

fn fn_id(n: u64) -> FnId {
    FnId(DefHash::new(0, n))
}

/// Builds one function, handing out locals, sites and spans.
struct Fb {
    decl: FnDecl,
    next_site: u32,
    next_span: u32,
}

impl Fb {
    fn new(id: u64, name: &str, mode: Mode, ret_ty: Ty) -> Self {
        let ret_mode = if mode == Mode::Exec {
            Mode::Exec
        } else {
            Mode::Spec
        };
        Self {
            decl: FnDecl {
                id: fn_id(id),
                name: name.to_string(),
                span: SpanId(0),
                mode,
                role: FnRole::Item,
                kind: Default::default(),
                type_params: Vec::new(),
                locals: vec![LocalDecl {
                    name: "result".to_string(),
                    ty: ret_ty,
                    mode: ret_mode,
                    prophecy: trust_vc_vcir::DeclProphecy::Default,
                    mutable: false,
                    kind: LocalKind::Return,
                    span: SpanId(0),
                }],
                params: Vec::new(),
                ret: LocalId(0),
                requires: Vec::new(),
                ensures: Vec::new(),
                recommends: Vec::new(),
                decreases: Vec::new(),
                decreases_when: None,
                decreases_by: None,
                unwind: None,
                attrs: FnAttrs::default(),
                body: Body::None,
            },
            next_site: 0,
            next_span: 1,
        }
    }

    fn span(&mut self) -> SpanId {
        self.next_span += 1;
        SpanId(self.next_span)
    }

    fn site(&mut self) -> SiteId {
        self.next_site += 1;
        SiteId(self.next_site)
    }

    fn local_mode(&self) -> Mode {
        if self.decl.mode == Mode::Exec {
            Mode::Exec
        } else {
            Mode::Spec
        }
    }

    fn add_local(&mut self, name: &str, ty: Ty, mutable: bool, kind: LocalKind) -> LocalId {
        let span = self.span();
        let mode = if kind == LocalKind::Bound {
            Mode::Spec
        } else {
            self.local_mode()
        };
        let id = LocalId(u32::try_from(self.decl.locals.len()).unwrap());
        self.decl.locals.push(LocalDecl {
            name: name.to_string(),
            ty,
            mode,
            prophecy: trust_vc_vcir::DeclProphecy::Default,
            mutable,
            kind,
            span,
        });
        id
    }

    fn param(&mut self, name: &str, ty: Ty) -> LocalId {
        let id = self.add_local(name, ty, false, LocalKind::Param);
        self.decl.params.push(id);
        id
    }

    fn mut_param(&mut self, name: &str, ty: Ty) -> LocalId {
        let id = self.add_local(name, ty, true, LocalKind::Param);
        self.decl.params.push(id);
        id
    }

    fn let_local(&mut self, name: &str, ty: Ty) -> LocalId {
        self.add_local(name, ty, true, LocalKind::Let)
    }

    fn rd(&mut self, local: LocalId) -> Expr {
        let ty = self.decl.locals[local.index()].ty.clone();
        let span = self.span();
        Expr::read(Place::local(local), ty, span)
    }

    fn lit(&mut self, value: i128, ty: Ty) -> Expr {
        let span = self.span();
        Expr::int_lit(value, ty, span)
    }

    fn tt(&mut self, value: bool) -> Expr {
        let span = self.span();
        Expr::bool_lit(value, span)
    }

    fn bin(&mut self, op: BinOp, lhs: Expr, rhs: Expr, ty: Ty) -> Expr {
        let span = self.span();
        Expr::binary(op, lhs, rhs, ty, span)
    }

    fn cmp(&mut self, op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
        self.bin(op, lhs, rhs, Ty::Bool)
    }

    fn checked(&mut self, op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
        let ty = lhs.ty.clone();
        let site = self.site();
        let span = self.span();
        Expr::checked_binary(op, lhs, rhs, ty, site, span)
    }

    fn int_of(&mut self, expr: Expr) -> Expr {
        let span = self.span();
        expr.cast(CastKind::Exact, Ty::int(), span)
    }

    fn call(&mut self, callee: FnId, args: Vec<Expr>, ty: Ty) -> Expr {
        let span = self.span();
        Expr::new(
            ty,
            span,
            ExprKind::Call {
                callee,
                type_args: Vec::new(),
                args,
            },
        )
    }

    fn clause(&mut self, expr: Expr) -> Clause {
        let span = self.span();
        Clause {
            expr,
            span,
            attrs: ClauseAttrs::default(),
        }
    }

    fn requires(&mut self, expr: Expr) {
        let clause = self.clause(expr);
        self.decl.requires.push(clause);
    }

    fn ensures(&mut self, expr: Expr) {
        let clause = self.clause(expr);
        self.decl.ensures.push(clause);
    }

    fn stmt(&mut self, kind: StmtKind) -> Stmt {
        let span = self.span();
        Stmt::new(span, kind)
    }

    fn assert(&mut self, expr: Expr) -> Stmt {
        let site = self.site();
        self.stmt(StmtKind::Assert {
            expr,
            site,
            attrs: ClauseAttrs::default(),
        })
    }

    fn assume(&mut self, expr: Expr) -> Stmt {
        self.stmt(StmtKind::Assume {
            expr,
            attrs: ClauseAttrs::default(),
        })
    }

    fn let_stmt(&mut self, local: LocalId, init: Option<Expr>) -> Stmt {
        self.stmt(StmtKind::Let { local, init })
    }

    fn assign(&mut self, local: LocalId, value: Expr) -> Stmt {
        self.stmt(StmtKind::Assign {
            place: Place::local(local),
            value,
        })
    }

    fn ret(&mut self, value: Option<Expr>) -> Stmt {
        let site = self.site();
        self.stmt(StmtKind::Return { value, site })
    }

    fn call_stmt(&mut self, callee: FnId, args: Vec<Expr>, dest: Option<Place>) -> Stmt {
        let site = self.site();
        self.stmt(StmtKind::Call {
            callee,
            type_args: Vec::new(),
            args,
            dest,
            site,
        })
    }

    /// A loop with isolation unless `joined`; `cond` is a `while`
    /// condition without statements.
    fn looped(
        &mut self,
        id: u32,
        cond: Option<Expr>,
        invariants: Vec<(InvariantKind, Expr)>,
        decreases: Vec<Expr>,
        body: Vec<Stmt>,
        joined: bool,
    ) -> Stmt {
        let invariants = invariants
            .into_iter()
            .map(|(kind, expr)| {
                let span = self.span();
                LoopInvariant { kind, expr, span }
            })
            .collect();
        let sites = LoopSites {
            entry: self.site(),
            end: self.site(),
            exit: self.site(),
        };
        self.stmt(StmtKind::Loop(Box::new(Loop {
            id: LoopId(id),
            isolation: !joined,
            allow_complex_invariants: false,
            cond: cond.map(|expr| LoopCond {
                block: Block::default(),
                expr,
            }),
            invariants,
            decreases,
            body: Block::new(body),
            sites,
        })))
    }

    fn brk(&mut self, target: u32) -> Stmt {
        let site = self.site();
        self.stmt(StmtKind::Break {
            target: LoopId(target),
            site,
        })
    }

    fn cont(&mut self, target: u32) -> Stmt {
        let site = self.site();
        self.stmt(StmtKind::Continue {
            target: LoopId(target),
            site,
        })
    }

    fn if_then(&mut self, cond: Expr, then: Vec<Stmt>) -> Stmt {
        self.stmt(StmtKind::If {
            cond,
            then_block: Block::new(then),
            else_block: Block::default(),
        })
    }

    /// `n - x` as `int`, for measures.
    fn minus(&mut self, n: i128, x: LocalId) -> Expr {
        let lit = self.lit(n, Ty::int());
        let rx = self.rd(x);
        let ix = self.int_of(rx);
        self.bin(BinOp::Sub, lit, ix, Ty::int())
    }

    /// `x = x + 1`, checked.
    fn incr(&mut self, x: LocalId) -> Stmt {
        let ty = self.decl.locals[x.index()].ty.clone();
        let (rx, one) = (self.rd(x), self.lit(1, ty));
        let sum = self.checked(BinOp::Add, rx, one);
        self.assign(x, sum)
    }

    /// `x op n` for a local of a machine type.
    fn cmp_lit(&mut self, op: BinOp, x: LocalId, n: i128) -> Expr {
        let ty = self.decl.locals[x.index()].ty.clone();
        let (rx, lit) = (self.rd(x), self.lit(n, ty));
        self.cmp(op, rx, lit)
    }

    fn body(mut self, stmts: Vec<Stmt>) -> FnDecl {
        self.decl.body = Body::Stmts(Block::new(stmts));
        self.decl
    }

    fn spec_body(mut self, expr: Expr) -> FnDecl {
        self.decl.body = Body::Spec(expr);
        self.decl
    }
}

fn krate(fns: Vec<FnDecl>) -> VcCrate {
    let mut krate = VcCrate::new("test_crate");
    krate.fns = fns;
    krate
}

/// Well-formedness is the generator's precondition.
#[track_caller]
fn checks_of(krate: &VcCrate, id: u64) -> Vec<Check> {
    let problems = check_crate(krate);
    assert!(problems.is_empty(), "malformed test crate: {problems:#?}");
    match generate(krate).get(fn_id(id)) {
        Some(FnVcs::Checks(checks)) => checks.clone(),
        other => panic!("expected checks for function {id}, got {other:?}"),
    }
}

fn solve(check: &Check) -> Verdict {
    trust_vc_vcir::solve::check(&check.query, "test", &Limits::default())
}

/// The verdict of every check, in order, as `P` (proved), `R` (refuted) or
/// `?` (anything else).
fn verdicts(checks: &[Check]) -> String {
    checks
        .iter()
        .map(|c| match solve(c) {
            Verdict::Proved { .. } => 'P',
            Verdict::Refuted { .. } => 'R',
            _ => '?',
        })
        .collect()
}

// ----------------------------------------------------------------------
// Assertions, assumptions, requires
// ----------------------------------------------------------------------

/// `assert(true); assert(true && false); assert(false);` reports one
/// failure: an assertion is assumed after its site (basic.rs `test1_fails`).
#[test]
fn a_failed_assertion_is_assumed_afterwards() {
    let mut f = Fb::new(1, "test1", Mode::Exec, Ty::Unit);
    let t = f.tt(true);
    let a1 = f.assert(t);
    let (t, u) = (f.tt(true), f.tt(false));
    let conj = f.bin(BinOp::And, t, u, Ty::Bool);
    let a2 = f.assert(conj);
    let u = f.tt(false);
    let a3 = f.assert(u);
    let r = f.ret(None);
    let k = krate(vec![f.body(vec![a1, a2, a3, r])]);
    assert_eq!(verdicts(&checks_of(&k, 1)), "PRP");
}

/// Preconditions hold on entry; an assumption is a fact.
#[test]
fn requires_and_assume_are_facts() {
    let build = |bound: i128| {
        let mut f = Fb::new(1, "f", Mode::Exec, Ty::Unit);
        let x = f.param("x", Ty::int());
        let y = f.param("y", Ty::int());
        let (rx, zero) = (f.rd(x), f.lit(0, Ty::int()));
        let pre = f.cmp(BinOp::Gt, rx, zero);
        f.requires(pre);
        let (ry, rx) = (f.rd(y), f.rd(x));
        let fact = f.cmp(BinOp::Ge, ry, rx);
        let assume = f.assume(fact);
        let (ry, b) = (f.rd(y), f.lit(bound, Ty::int()));
        let goal = f.cmp(BinOp::Gt, ry, b);
        let a = f.assert(goal);
        let r = f.ret(None);
        krate(vec![f.body(vec![assume, a, r])])
    };
    assert_eq!(verdicts(&checks_of(&build(0), 1)), "P");
    // Liar: y > x > 0 does not give y > 1.
    assert_eq!(verdicts(&checks_of(&build(1), 1)), "R");
}

// ----------------------------------------------------------------------
// Exec arithmetic
// ----------------------------------------------------------------------

/// `let y = x + 1` on `u8` overflows unless `x < 255`; the range fact of `y`
/// must not prove the check that justifies it.
#[test]
fn overflow_is_checked_before_the_result_is_named() {
    let build = |bounded: bool| {
        let mut f = Fb::new(1, "f", Mode::Exec, Ty::Unit);
        let x = f.param("x", Ty::uint(8));
        if bounded {
            let (rx, lim) = (f.rd(x), f.lit(255, Ty::uint(8)));
            let pre = f.cmp(BinOp::Lt, rx, lim);
            f.requires(pre);
        }
        let y = f.let_local("y", Ty::uint(8));
        let (rx, one) = (f.rd(x), f.lit(1, Ty::uint(8)));
        let sum = f.checked(BinOp::Add, rx, one);
        let l = f.let_stmt(y, Some(sum));
        // After the check the exact value is known.
        let (ry, rx) = (f.rd(y), f.rd(x));
        let gt = f.cmp(BinOp::Gt, ry, rx);
        let a = f.assert(gt);
        let r = f.ret(None);
        krate(vec![f.body(vec![l, a, r])])
    };
    let checks = checks_of(&build(false), 1);
    assert!(matches!(checks[0].kind, CheckKind::Overflow { .. }));
    assert_eq!(verdicts(&checks), "RP");
    assert_eq!(verdicts(&checks_of(&build(true), 1)), "PP");
}

/// Division by zero is checked; the quotient of unsigned values is exact.
#[test]
fn division_by_zero_is_checked() {
    let build = |nonzero: bool| {
        let mut f = Fb::new(1, "f", Mode::Exec, Ty::Unit);
        let x = f.param("x", Ty::uint(32));
        if nonzero {
            let x2 = f.rd(x);
            let zero = f.lit(0, Ty::uint(32));
            let pre = f.cmp(BinOp::Gt, x2, zero);
            f.requires(pre);
        }
        let q = f.let_local("q", Ty::uint(32));
        let (hundred, rx) = (f.lit(100, Ty::uint(32)), f.rd(x));
        let div = f.checked(BinOp::Div, hundred, rx);
        let l = f.let_stmt(q, Some(div));
        let r = f.ret(None);
        krate(vec![f.body(vec![l, r])])
    };
    let checks = checks_of(&build(false), 1);
    assert!(matches!(checks[0].kind, CheckKind::DivByZero { .. }));
    assert_eq!(verdicts(&checks), "R");
    assert_eq!(verdicts(&checks_of(&build(true), 1)), "P");
}

/// Proof-mode machine arithmetic is Verus's clip: the result is in range,
/// but its value out of range is unknown (basic.rs `test_compound_assign`,
/// `test2a`).
#[test]
fn as_casts_clip_like_verus() {
    let build = |claim: i128, less: bool| {
        let mut f = Fb::new(1, "test2a", Mode::Proof, Ty::Unit);
        let x = f.let_local("x", Ty::uint(8));
        let init = f.lit(200, Ty::uint(8));
        let l = f.let_stmt(x, Some(init));
        let rx = f.rd(x);
        let ix = f.int_of(rx);
        let hundred = f.lit(100, Ty::uint(8));
        let ih = f.int_of(hundred);
        let sum = f.bin(BinOp::Add, ix, ih, Ty::int());
        let span = f.span();
        let clipped = sum.cast(CastKind::As, Ty::uint(8), span);
        let assign = f.assign(x, clipped);
        let rx = f.rd(x);
        let ix = f.int_of(rx);
        let c = f.lit(claim, Ty::int());
        let goal = if less {
            f.cmp(BinOp::Lt, ix, c)
        } else {
            f.cmp(BinOp::Eq, ix, c)
        };
        let a = f.assert(goal);
        let r = f.ret(None);
        krate(vec![f.body(vec![l, assign, a, r])])
    };
    assert_eq!(verdicts(&checks_of(&build(256, true), 1)), "P");
    // Liar: Rust would give 44; Verus's clip does not say which value.
    assert_eq!(verdicts(&checks_of(&build(44, false), 1)), "R");
}

// ----------------------------------------------------------------------
// Calls, returns, joins
// ----------------------------------------------------------------------

/// `proof fn add(a, b) -> r requires a <= b ensures r == a + b`, and a
/// caller: the precondition is checked at the call, the postcondition
/// assumed after it.
#[test]
fn calls_use_the_callee_contract() {
    let callee = || {
        let mut f = Fb::new(1, "add", Mode::Proof, Ty::int());
        let a = f.param("a", Ty::int());
        let b = f.param("b", Ty::int());
        let (ra, rb) = (f.rd(a), f.rd(b));
        let pre = f.cmp(BinOp::Le, ra, rb);
        f.requires(pre);
        let (ret, ra, rb) = (f.rd(LocalId(0)), f.rd(a), f.rd(b));
        let sum = f.bin(BinOp::Add, ra, rb, Ty::int());
        let post = f.cmp(BinOp::Eq, ret, sum);
        f.ensures(post);
        let (ra, rb) = (f.rd(a), f.rd(b));
        let sum = f.bin(BinOp::Add, ra, rb, Ty::int());
        let r = f.ret(Some(sum));
        f.body(vec![r])
    };
    let build = |first: i128, second: i128, claim: i128| {
        let mut f = Fb::new(2, "caller", Mode::Proof, Ty::Unit);
        let d = f.let_local("d", Ty::int());
        let l = f.let_stmt(d, None);
        let (x, y) = (f.lit(first, Ty::int()), f.lit(second, Ty::int()));
        let c = f.call_stmt(fn_id(1), vec![x, y], Some(Place::local(d)));
        let (rd, want) = (f.rd(d), f.lit(claim, Ty::int()));
        let goal = f.cmp(BinOp::Eq, rd, want);
        let a = f.assert(goal);
        let r = f.ret(None);
        krate(vec![callee(), f.body(vec![l, c, a, r])])
    };
    let k = build(1, 2, 3);
    assert_eq!(
        verdicts(&checks_of(&k, 1)),
        "P",
        "the callee's own postcondition"
    );
    let checks = checks_of(&k, 2);
    assert!(matches!(
        checks[0].kind,
        CheckKind::Precondition { clause: 0, .. }
    ));
    assert_eq!(verdicts(&checks), "PP");
    // Liars: a violated precondition, a wrong claim about the result.
    assert_eq!(verdicts(&checks_of(&build(2, 1, 3), 2)), "RP");
    assert_eq!(verdicts(&checks_of(&build(1, 2, 4), 2)), "PR");
}

/// `proof fn id(a) -> r ensures #![verifier::proof_note("n")] r == a`: the
/// labelled clause is checked at `id`'s exit but a caller cannot assume it
/// (basic.rs `test_ret2` with its first `ensures` clause deleted). The twin
/// without the label proves the caller's assertion.
#[test]
fn labelled_ensures_are_not_assumed_by_callers() {
    let build = |attrs: ClauseAttrs| {
        let mut f = Fb::new(1, "id", Mode::Proof, Ty::int());
        let a = f.param("a", Ty::int());
        let (ret, ra) = (f.rd(LocalId(0)), f.rd(a));
        let post = f.cmp(BinOp::Eq, ret, ra);
        let mut clause = f.clause(post);
        clause.attrs = attrs;
        f.decl.ensures.push(clause);
        let ra = f.rd(a);
        let r = f.ret(Some(ra));
        let callee = f.body(vec![r]);

        let mut f = Fb::new(2, "caller", Mode::Proof, Ty::Unit);
        let d = f.let_local("d", Ty::int());
        let l = f.let_stmt(d, None);
        let x = f.lit(7, Ty::int());
        let c = f.call_stmt(fn_id(1), vec![x], Some(Place::local(d)));
        let (rd, want) = (f.rd(d), f.lit(7, Ty::int()));
        let goal = f.cmp(BinOp::Eq, rd, want);
        let a = f.assert(goal);
        let r = f.ret(None);
        krate(vec![callee, f.body(vec![l, c, a, r])])
    };
    let note = ClauseAttrs {
        proof_notes: vec!["n".to_string()],
        custom_errs: Vec::new(),
    };
    let custom = ClauseAttrs {
        proof_notes: Vec::new(),
        custom_errs: vec!["c".to_string()],
    };
    for attrs in [note, custom] {
        let k = build(attrs);
        assert_eq!(verdicts(&checks_of(&k, 1)), "P", "checked at the exit");
        assert_eq!(
            verdicts(&checks_of(&k, 2)),
            "R",
            "not assumed by the caller"
        );
    }
    // Twin: the same clause without a label is assumed.
    assert_eq!(verdicts(&checks_of(&build(ClauseAttrs::default()), 2)), "P");
}

/// In a postcondition a parameter means its value on entry (basic.rs
/// `test_mut_param`), and a failure names the clause.
#[test]
fn postconditions_read_parameters_at_entry() {
    let build = |claim: i128, op: BinOp| {
        let mut f = Fb::new(1, "test1", Mode::Exec, Ty::Unit);
        let x = f.mut_param("x", Ty::uint(32));
        let (rx, ten) = (f.rd(x), f.lit(10, Ty::uint(32)));
        let pre = f.cmp(BinOp::Lt, rx, ten);
        f.requires(pre);
        let (rx, c) = (f.rd(x), f.lit(claim, Ty::uint(32)));
        let post = f.cmp(op, rx, c);
        f.ensures(post);
        let hundred = f.lit(100, Ty::uint(32));
        let assign = f.assign(x, hundred);
        let r = f.ret(None);
        krate(vec![f.body(vec![assign, r])])
    };
    let checks = checks_of(&build(10, BinOp::Lt), 1);
    assert!(matches!(
        checks[0].kind,
        CheckKind::Postcondition { clause: 0, .. }
    ));
    assert_eq!(verdicts(&checks), "P");
    assert_eq!(verdicts(&checks_of(&build(100, BinOp::Eq), 1)), "R");
}

/// `let x: u64; if a { x = 1 } else { x = 2 }` (basic.rs
/// `test_decl_init_let_fail`, `test2`).
#[test]
fn branches_join() {
    let build = |claim_under_a: bool| {
        let mut f = Fb::new(1, "test2", Mode::Exec, Ty::Unit);
        let a = f.param("a", Ty::Bool);
        let x = f.let_local("x", Ty::uint(64));
        let l = f.let_stmt(x, None);
        let one = f.lit(1, Ty::uint(64));
        let then_assign = f.assign(x, one);
        let two = f.lit(2, Ty::uint(64));
        let else_assign = f.assign(x, two);
        let ra = f.rd(a);
        let branch = f.stmt(StmtKind::If {
            cond: ra,
            then_block: Block::new(vec![then_assign]),
            else_block: Block::new(vec![else_assign]),
        });
        let (rx, one) = (f.rd(x), f.lit(1, Ty::uint(64)));
        let is_one = f.cmp(BinOp::Eq, rx, one);
        let goal = if claim_under_a {
            let ra = f.rd(a);
            f.bin(BinOp::Implies, ra, is_one, Ty::Bool)
        } else {
            is_one
        };
        let check = f.assert(goal);
        let r = f.ret(None);
        krate(vec![f.body(vec![l, branch, check, r])])
    };
    assert_eq!(verdicts(&checks_of(&build(true), 1)), "P");
    assert_eq!(verdicts(&checks_of(&build(false), 1)), "R");
}

/// A checked operation on the right of `&&` is checked only when the left
/// side holds (basic.rs `test_short_circuit`).
#[test]
fn checks_under_short_circuit_are_guarded() {
    let mut f = Fb::new(1, "f", Mode::Exec, Ty::Unit);
    let x = f.param("x", Ty::uint(8));
    let b = f.let_local("b", Ty::Bool);
    let (rx, lim) = (f.rd(x), f.lit(255, Ty::uint(8)));
    let small = f.cmp(BinOp::Lt, rx, lim);
    let (rx, one) = (f.rd(x), f.lit(1, Ty::uint(8)));
    let sum = f.checked(BinOp::Add, rx, one);
    let zero = f.lit(0, Ty::uint(8));
    let positive = f.cmp(BinOp::Gt, sum, zero);
    let guarded = f.bin(BinOp::And, small, positive, Ty::Bool);
    let l = f.let_stmt(b, Some(guarded));
    let r = f.ret(None);
    let k = krate(vec![f.body(vec![l, r])]);
    assert_eq!(verdicts(&checks_of(&k, 1)), "P");

    // Liar: the same operation unguarded.
    let mut f = Fb::new(1, "f", Mode::Exec, Ty::Unit);
    let x = f.param("x", Ty::uint(8));
    let b = f.let_local("b", Ty::Bool);
    let (rx, one) = (f.rd(x), f.lit(1, Ty::uint(8)));
    let sum = f.checked(BinOp::Add, rx, one);
    let zero = f.lit(0, Ty::uint(8));
    let positive = f.cmp(BinOp::Gt, sum, zero);
    let l = f.let_stmt(b, Some(positive));
    let r = f.ret(None);
    let k = krate(vec![f.body(vec![l, r])]);
    assert_eq!(verdicts(&checks_of(&k, 1)), "R");
}

// ----------------------------------------------------------------------
// Spec functions
// ----------------------------------------------------------------------

/// `spec fn f1(i, j) = i <= j` is visible; `#[verifier(opaque)] spec fn
/// f3(i, j) = f1(j, i)` only after `reveal` (basic.rs `test_spec_fn`).
#[test]
fn spec_definitions_follow_reveal_and_hide() {
    let spec_fns = || {
        let mut f1 = Fb::new(1, "f1", Mode::Spec, Ty::Bool);
        let i = f1.param("i", Ty::int());
        let j = f1.param("j", Ty::int());
        let (ri, rj) = (f1.rd(i), f1.rd(j));
        let body = f1.cmp(BinOp::Le, ri, rj);
        let f1 = f1.spec_body(body);
        let mut f3 = Fb::new(3, "f3", Mode::Spec, Ty::Bool);
        f3.decl.attrs.opaque = true;
        let i = f3.param("i", Ty::int());
        let j = f3.param("j", Ty::int());
        let (rj, ri) = (f3.rd(j), f3.rd(i));
        let body = f3.call(fn_id(1), vec![rj, ri], Ty::Bool);
        (f1, f3.spec_body(body))
    };
    // assert(f3(b, a)) with a <= b assumed, with or without reveal(f3).
    let build = |reveal: bool, hide_f1: bool| {
        let (f1, f3) = spec_fns();
        let mut t = Fb::new(4, "t", Mode::Proof, Ty::Unit);
        let a = t.param("a", Ty::int());
        let b = t.param("b", Ty::int());
        let mut stmts = Vec::new();
        if hide_f1 {
            stmts.push(t.stmt(StmtKind::Hide { callee: fn_id(1) }));
        }
        let (ra, rb) = (t.rd(a), t.rd(b));
        let le = t.cmp(BinOp::Le, ra, rb);
        stmts.push(t.assume(le));
        if reveal {
            stmts.push(t.stmt(StmtKind::Reveal {
                callee: fn_id(3),
                fuel: None,
            }));
        }
        let (rb, ra) = (t.rd(b), t.rd(a));
        let call = t.call(fn_id(3), vec![rb, ra], Ty::Bool);
        stmts.push(t.assert(call));
        stmts.push(t.ret(None));
        krate(vec![f1, f3, t.body(stmts)])
    };
    assert_eq!(verdicts(&checks_of(&build(true, false), 4)), "P");
    assert_eq!(verdicts(&checks_of(&build(false, false), 4)), "R");
    assert_eq!(verdicts(&checks_of(&build(true, true), 4)), "R");
}

/// A reveal supplies the definition only within its conditional branch.
#[test]
fn branch_reveal_is_scoped() {
    let build = |liar: bool, reveal_else: bool, check_after: bool, assert_inside: bool| {
        let mut one = Fb::new(1, "one", Mode::Spec, Ty::int());
        one.decl.attrs.opaque = true;
        let value = one.lit(1, Ty::int());
        let one = one.spec_body(value);
        let mut t = Fb::new(2, "t", Mode::Proof, Ty::Unit);
        let b = t.param("b", Ty::Bool);
        let reveal = t.stmt(StmtKind::Reveal {
            callee: fn_id(1),
            fuel: None,
        });
        let call = t.call(fn_id(1), vec![], Ty::int());
        let value = t.lit(if liar { 2 } else { 1 }, Ty::int());
        let goal = t.cmp(BinOp::Eq, call, value);
        let assertion = t.assert(goal.clone());
        let else_assertion = t.assert(goal.clone());
        let mut then_stmts = vec![reveal.clone()];
        let mut else_stmts = if reveal_else { vec![reveal] } else { vec![] };
        if assert_inside {
            then_stmts.push(assertion);
            else_stmts.push(else_assertion);
        }
        let cond = t.rd(b);
        let branch = t.stmt(StmtKind::If {
            cond,
            then_block: Block::new(then_stmts),
            else_block: Block::new(else_stmts),
        });
        let mut stmts = vec![branch];
        if check_after {
            stmts.push(t.assert(goal));
        }
        stmts.push(t.ret(None));
        krate(vec![one, t.body(stmts)])
    };
    assert_eq!(
        verdicts(&checks_of(&build(false, true, false, true), 2)),
        "PP"
    );
    assert_eq!(
        verdicts(&checks_of(&build(true, true, false, true), 2)),
        "RR"
    );
    // The then-branch reveal must not make the else assertion provable.
    assert_eq!(
        verdicts(&checks_of(&build(false, false, false, true), 2)),
        "PR"
    );
    // Proven branch assertions remain usable after the join.
    assert_eq!(
        verdicts(&checks_of(&build(false, true, true, true), 2)),
        "PPP"
    );
    // Both branches reveal the same definition, so it holds after the join.
    assert_eq!(
        verdicts(&checks_of(&build(false, true, true, false), 2)),
        "P"
    );
    // A reveal on only one continuing path cannot escape the branch.
    assert_eq!(
        verdicts(&checks_of(&build(false, false, true, false), 2)),
        "R"
    );
}

/// A spec definition Verus emits after checking the function
/// (`DefOrder::Later`) stays uninterpreted there, `reveal` included; one
/// whose order is unknown (`DefOrder::Unknown`) too, and its check is marked
/// so that a refutation is not a verdict. `spec fn one() -> int { 1 }` and
/// `proof fn t() { reveal(one); assert(one() == 1); }`, with the liar
/// `assert(one() == 2)`.
#[test]
fn spec_definitions_follow_verus_order() {
    let build = |claim: i128, order: Option<DefOrder>| {
        let mut one = Fb::new(1, "one", Mode::Spec, Ty::int());
        let body = one.lit(1, Ty::int());
        let one = one.spec_body(body);
        let mut t = Fb::new(2, "t", Mode::Proof, Ty::Unit);
        let reveal = t.stmt(StmtKind::Reveal {
            callee: fn_id(1),
            fuel: None,
        });
        let call = t.call(fn_id(1), vec![], Ty::int());
        let want = t.lit(claim, Ty::int());
        let eq = t.cmp(BinOp::Eq, call, want);
        let a = t.assert(eq);
        let r = t.ret(None);
        let mut krate = krate(vec![one, t.body(vec![reveal, a, r])]);
        if let Some(order) = order {
            krate
                .def_order
                .insert(fn_id(2), [(fn_id(1), order)].into_iter().collect());
        }
        krate
    };
    let checks = checks_of(&build(1, None), 2);
    assert!(!checks[0].order_unknown);
    assert_eq!(verdicts(&checks), "P");
    assert_eq!(verdicts(&checks_of(&build(2, None), 2)), "R");
    let checks = checks_of(&build(1, Some(DefOrder::Later)), 2);
    assert!(!checks[0].order_unknown);
    assert_eq!(verdicts(&checks), "R");
    let checks = checks_of(&build(1, Some(DefOrder::Unknown)), 2);
    assert!(checks[0].order_unknown);
    assert_eq!(verdicts(&checks), "R");
}

/// `hide` is a header only among the body's leading statements; a plain
/// block of nothing but `hide`s counts as its `hide`s, and any other
/// statement, an empty block or ghost block included, ends the headers.
#[test]
fn hide_headers_end_at_any_other_statement() {
    let f1 = || {
        let mut f1 = Fb::new(1, "f1", Mode::Spec, Ty::Bool);
        let i = f1.param("i", Ty::int());
        let j = f1.param("j", Ty::int());
        let (ri, rj) = (f1.rd(i), f1.rd(j));
        let body = f1.cmp(BinOp::Le, ri, rj);
        f1.spec_body(body)
    };
    // `prefix(t)` comes first; then assume(a <= b); assert(f1(a, b)).
    let build = |mode: Mode, prefix: &dyn Fn(&mut Fb) -> Vec<Stmt>| {
        let mut t = Fb::new(2, "t", mode, Ty::Unit);
        let a = t.param("a", Ty::int());
        let b = t.param("b", Ty::int());
        let mut stmts = prefix(&mut t);
        let (ra, rb) = (t.rd(a), t.rd(b));
        let le = t.cmp(BinOp::Le, ra, rb);
        let assume = t.assume(le);
        let (ra, rb) = (t.rd(a), t.rd(b));
        let call = t.call(fn_id(1), vec![ra, rb], Ty::Bool);
        let assert = t.assert(call);
        if mode == Mode::Exec {
            stmts.push(t.stmt(StmtKind::Ghost(Block::new(vec![assume, assert]))));
        } else {
            stmts.extend([assume, assert]);
        }
        stmts.push(t.ret(None));
        krate(vec![f1(), t.body(stmts)])
    };
    let hide = |t: &mut Fb| t.stmt(StmtKind::Hide { callee: fn_id(1) });
    assert_eq!(
        verdicts(&checks_of(&build(Mode::Proof, &|_| vec![]), 2)),
        "P"
    );
    let hidden_in_block = build(Mode::Proof, &|t| {
        let h = hide(t);
        vec![t.stmt(StmtKind::Block(Block::new(vec![h])))]
    });
    assert_eq!(verdicts(&checks_of(&hidden_in_block, 2)), "R");
    let after_empty_block = build(Mode::Proof, &|t| {
        vec![t.stmt(StmtKind::Block(Block::new(vec![]))), hide(t)]
    });
    assert_eq!(refusal_tag(&after_empty_block, 2), "hide-position");
    let hidden_first = build(Mode::Exec, &|t| {
        vec![hide(t), t.stmt(StmtKind::Ghost(Block::new(vec![])))]
    });
    assert_eq!(verdicts(&checks_of(&hidden_first, 2)), "R");
    let after_ghost_block = build(Mode::Exec, &|t| {
        vec![t.stmt(StmtKind::Ghost(Block::new(vec![]))), hide(t)]
    });
    assert_eq!(refusal_tag(&after_ghost_block, 2), "hide-position");
}

/// A spec function that calls itself outside a group of recursive
/// functions has no admitted definition, and a function using it is
/// refused rather than checked with it left uninterpreted.
#[test]
fn recursive_spec_functions_are_refused() {
    let mut f = Fb::new(1, "f", Mode::Spec, Ty::int());
    let x = f.param("x", Ty::int());
    let rx = f.rd(x);
    let call = f.call(fn_id(1), vec![rx], Ty::int());
    let one = f.lit(1, Ty::int());
    let body = f.bin(BinOp::Add, call, one, Ty::int());
    let f = f.spec_body(body);
    let mut t = Fb::new(2, "t", Mode::Proof, Ty::Unit);
    let z = t.lit(0, Ty::int());
    let call = t.call(fn_id(1), vec![z], Ty::int());
    let z = t.lit(0, Ty::int());
    let goal = t.cmp(BinOp::Gt, call, z);
    let a = t.assert(goal);
    let r = t.ret(None);
    let k = krate(vec![f, t.body(vec![a, r])]);
    assert!(check_crate(&k).is_empty());
    let vcs = generate(&k);
    for (id, tag) in [(1, "recursion"), (2, "recursive-spec-fn")] {
        match vcs.get(fn_id(id)) {
            Some(FnVcs::Refused(refusal)) => assert_eq!(refusal.tag, tag),
            other => panic!("function {id}: expected a refusal, got {other:?}"),
        }
    }
}

/// A product of two variables is an uninterpreted stand-in with Verus's
/// axiom, and the query says it is approximate.
#[test]
fn nonlinear_products_are_approximate() {
    let build = |claim_nonneg: bool| {
        let mut f = Fb::new(1, "f", Mode::Proof, Ty::Unit);
        let x = f.param("x", Ty::nat());
        let y = f.param("y", Ty::nat());
        let (rx, ry) = (f.rd(x), f.rd(y));
        let (ix, iy) = (f.int_of(rx), f.int_of(ry));
        let prod = f.bin(BinOp::Mul, ix, iy, Ty::int());
        let zero = f.lit(0, Ty::int());
        let goal = if claim_nonneg {
            f.cmp(BinOp::Ge, prod, zero)
        } else {
            f.cmp(BinOp::Gt, prod, zero)
        };
        let a = f.assert(goal);
        let r = f.ret(None);
        krate(vec![f.body(vec![a, r])])
    };
    let checks = checks_of(&build(true), 1);
    assert!(checks[0].approximate);
    assert_eq!(verdicts(&checks), "P", "Verus's prelude_mul_nats");
    let checks = checks_of(&build(false), 1);
    assert!(matches!(
        check(&checks[0].query, "liar", &Limits::default()),
        Verdict::Refuted { .. }
    ));
}

// ----------------------------------------------------------------------
// Data types
// ----------------------------------------------------------------------

/// `struct Foo { b: bool }`, `spec fn get_b(foo: Foo) -> bool { foo.b }` and
/// `fn test1() -> (b: Foo) ensures get_b(b) { Foo { b: true } }` (basic.rs
/// `test_ensures_type_inference`).
#[test]
fn structs_are_flattened() {
    let foo = AdtId(DefHash::new(1, 1));
    let adt = AdtDecl {
        id: foo,
        name: "Foo".to_string(),
        type_params: Vec::new(),
        span: SpanId(0),
        kind: AdtKind::Struct,
        variants: vec![VariantDecl {
            name: "Foo".to_string(),
            fields: vec![FieldDecl {
                name: "b".to_string(),
                ty: Ty::Bool,
                mode: Mode::Exec,
            }],
        }],
    };
    let build = |value: bool| {
        let mut g = Fb::new(1, "get_b", Mode::Spec, Ty::Bool);
        let p = g.param("foo", Ty::Adt(foo, Vec::new()));
        let span = g.span();
        let body = Expr::new(
            Ty::Bool,
            span,
            ExprKind::Read(Place {
                local: p,
                projections: vec![Projection::Field {
                    variant: 0,
                    field: 0,
                }],
            }),
        );
        let g = g.spec_body(body);
        let mut t = Fb::new(2, "test1", Mode::Exec, Ty::Adt(foo, Vec::new()));
        let ret = t.rd(LocalId(0));
        let post = t.call(fn_id(1), vec![ret], Ty::Bool);
        t.ensures(post);
        let b = t.tt(value);
        let span = t.span();
        let ctor = Expr::new(
            Ty::Adt(foo, Vec::new()),
            span,
            ExprKind::Ctor {
                adt: foo,
                variant: 0,
                fields: vec![b],
            },
        );
        let r = t.ret(Some(ctor));
        let mut k = krate(vec![g, t.body(vec![r])]);
        k.adts = vec![adt.clone()];
        k
    };
    assert_eq!(verdicts(&checks_of(&build(true), 2)), "P");
    assert_eq!(verdicts(&checks_of(&build(false), 2)), "R");
}

// ----------------------------------------------------------------------
// Rules Verus enforces that the generator refuses
// ----------------------------------------------------------------------

#[track_caller]
fn refusal_tag(krate: &VcCrate, id: u64) -> &'static str {
    assert!(check_crate(krate).is_empty(), "malformed test crate");
    match generate(krate).get(fn_id(id)) {
        Some(FnVcs::Refused(refusal)) => refusal.tag,
        other => panic!("expected a refusal, got {other:?}"),
    }
}

/// `hide` is a header in Verus (it holds for the whole body); after other
/// statements it is refused. `reveal_with_fuel` needs a `decreases` clause.
#[test]
fn hide_and_fuel_rules() {
    let spec = || {
        let mut f = Fb::new(1, "f", Mode::Spec, Ty::Bool);
        let body = f.tt(true);
        f.spec_body(body)
    };
    let mut t = Fb::new(2, "t", Mode::Proof, Ty::Unit);
    let yes = t.tt(true);
    let a = t.assert(yes);
    let hide = t.stmt(StmtKind::Hide { callee: fn_id(1) });
    let r = t.ret(None);
    let k = krate(vec![spec(), t.body(vec![a, hide, r])]);
    assert_eq!(refusal_tag(&k, 2), "hide-position");

    let mut t = Fb::new(2, "t", Mode::Proof, Ty::Unit);
    let reveal = t.stmt(StmtKind::Reveal {
        callee: fn_id(1),
        fuel: Some(2),
    });
    let r = t.ret(None);
    let k = krate(vec![spec(), t.body(vec![reveal, r])]);
    assert_eq!(refusal_tag(&k, 2), "reveal-with-fuel");
}

/// A precondition must read a `&mut` parameter through `old`; code that
/// runs may not use `old` at all.
#[test]
fn mut_ref_rules() {
    let mref = Ty::Ref {
        mutable: true,
        inner: Box::new(Ty::uint(64)),
    };
    let deref = |f: &mut Fb, local: LocalId| {
        let span = f.span();
        Expr::new(Ty::uint(64), span, ExprKind::Read(Place::deref(local)))
    };
    let mut f = Fb::new(1, "add1", Mode::Exec, Ty::Unit);
    let a = f.param("a", mref.clone());
    let (cur, ten) = (deref(&mut f, a), f.lit(10, Ty::uint(64)));
    let pre = f.cmp(BinOp::Lt, cur, ten);
    f.requires(pre);
    let r = f.ret(None);
    let k = krate(vec![f.body(vec![r])]);
    assert_eq!(refusal_tag(&k, 1), "mut-ref-requires");

    let mut f = Fb::new(1, "stuff", Mode::Exec, Ty::Unit);
    let x = f.param("x", mref);
    let y = f.let_local("y", Ty::uint(64));
    // Keep the Spec value well-moded; its Exec statement location is the refusal under test.
    f.decl.locals[y.index()].mode = Mode::Spec;
    let span = f.span();
    let old = Expr::new(Ty::uint(64), span, ExprKind::Old(Place::deref(x)));
    let l = f.let_stmt(y, Some(old));
    let r = f.ret(None);
    let k = krate(vec![f.body(vec![l, r])]);
    assert_eq!(refusal_tag(&k, 1), "old-in-exec");
}

// ----------------------------------------------------------------------
// Loops
// ----------------------------------------------------------------------

/// `let mut i: u32 = 0; while i < 10 invariant i <= 10 decreases 10 - i
/// { i = i + 1 } assert(i == 10)` (loops.rs `basic_while`): the invariant
/// and the negated condition give the assertion. Without the invariant
/// (`basic_while_fail1`) nothing bounds `i` after the loop.
#[test]
fn while_invariant_and_exit_condition() {
    let build = |with_invariant: bool| {
        let mut f = Fb::new(1, "test1", Mode::Exec, Ty::Unit);
        let i = f.let_local("i", Ty::uint(32));
        let zero = f.lit(0, Ty::uint(32));
        let l = f.let_stmt(i, Some(zero));
        let cond = f.cmp_lit(BinOp::Lt, i, 10);
        let mut invs = Vec::new();
        if with_invariant {
            invs.push((InvariantKind::Always, f.cmp_lit(BinOp::Le, i, 10)));
        }
        let measure = f.minus(10, i);
        let step = f.incr(i);
        let lp = f.looped(0, Some(cond), invs, vec![measure], vec![step], false);
        let done = f.cmp_lit(BinOp::Eq, i, 10);
        let a = f.assert(done);
        let r = f.ret(None);
        krate(vec![f.body(vec![l, lp, a, r])])
    };
    let checks = checks_of(&build(true), 1);
    let groups: Vec<QueryGroup> = checks.iter().map(|c| c.group).collect();
    assert!(matches!(
        checks[0].kind,
        CheckKind::LoopInvariant {
            at: InvariantAt::Entry,
            ..
        }
    ));
    assert_eq!(groups[0], QueryGroup::Body);
    assert!(matches!(groups[1], QueryGroup::Loop { index: 0, .. }));
    assert_eq!(*groups.last().unwrap(), QueryGroup::Body);
    // entry, overflow, end, decreases, assertion
    assert_eq!(verdicts(&checks), "PPPPP");
    // overflow, decreases, assertion
    assert_eq!(verdicts(&checks_of(&build(false), 1)), "PPR");
}

/// With isolation the body knows the invariants and nothing else: a
/// precondition must be repeated as an invariant. Without isolation the
/// body sees what held before the loop.
#[test]
fn isolation_forgets_what_held_before_the_loop() {
    let build = |invariant: bool, joined: bool| {
        let mut f = Fb::new(1, "f", Mode::Exec, Ty::Unit);
        let x = f.param("x", Ty::uint(32));
        let pre = f.cmp_lit(BinOp::Eq, x, 5);
        f.requires(pre);
        let i = f.let_local("i", Ty::uint(32));
        let zero = f.lit(0, Ty::uint(32));
        let l = f.let_stmt(i, Some(zero));
        let cond = f.cmp_lit(BinOp::Lt, i, 3);
        let mut invs = vec![(InvariantKind::Always, f.cmp_lit(BinOp::Le, i, 3))];
        if invariant {
            invs.push((InvariantKind::Always, f.cmp_lit(BinOp::Eq, x, 5)));
        }
        let measure = f.minus(3, i);
        let five = f.cmp_lit(BinOp::Eq, x, 5);
        let a = f.assert(five);
        let step = f.incr(i);
        let lp = f.looped(0, Some(cond), invs, vec![measure], vec![a, step], joined);
        let r = f.ret(None);
        krate(vec![f.body(vec![l, lp, r])])
    };
    let assertion = |k: &VcCrate| {
        let checks = checks_of(k, 1);
        let at = checks
            .iter()
            .position(|c| matches!(c.kind, CheckKind::Assert { .. }))
            .unwrap();
        verdicts(&checks[at..=at])
    };
    assert_eq!(assertion(&build(true, false)), "P");
    assert_eq!(assertion(&build(false, false)), "R");
    assert_eq!(assertion(&build(false, true)), "P");
}

/// `loop invariant_except_break i <= 10 ensures i == 10 { if i == 10 {
/// break } i = i + 1 }`: the `ensures` is checked at the `break` and known
/// after the loop.
#[test]
fn break_checks_the_loop_ensures() {
    let build = |target: i128| {
        let mut f = Fb::new(1, "f", Mode::Exec, Ty::Unit);
        let i = f.let_local("i", Ty::uint(32));
        let zero = f.lit(0, Ty::uint(32));
        let l = f.let_stmt(i, Some(zero));
        let invs = vec![
            (InvariantKind::ExceptBreak, f.cmp_lit(BinOp::Le, i, 10)),
            (InvariantKind::Ensures, f.cmp_lit(BinOp::Eq, i, target)),
        ];
        let measure = f.minus(10, i);
        let at_ten = f.cmp_lit(BinOp::Eq, i, 10);
        let b = f.brk(0);
        let exit = f.if_then(at_ten, vec![b]);
        let step = f.incr(i);
        let lp = f.looped(0, None, invs, vec![measure], vec![exit, step], false);
        let done = f.cmp_lit(BinOp::Eq, i, 10);
        let a = f.assert(done);
        let r = f.ret(None);
        krate(vec![f.body(vec![l, lp, a, r])])
    };
    let checks = checks_of(&build(10), 1);
    assert!(matches!(
        checks[1].kind,
        CheckKind::LoopInvariant {
            at: InvariantAt::Break(_),
            kind: InvariantKind::Ensures,
            ..
        }
    ));
    // entry, break, overflow, end, decreases, assertion
    assert_eq!(verdicts(&checks), "PPPPPP");
    assert_eq!(verdicts(&checks_of(&build(9), 1)), "PRPPPR");
}

/// Only what the loop assigns is havocked (loops.rs
/// `test_variables_not_havoc_basic` and `test_variables_havoc_basic`).
#[test]
fn only_assigned_locals_are_havocked() {
    let build = |assign_j: bool| {
        let mut f = Fb::new(1, "f", Mode::Exec, Ty::Unit);
        let i = f.let_local("i", Ty::uint(32));
        let j = f.let_local("j", Ty::uint(32));
        let zero = f.lit(0, Ty::uint(32));
        let li = f.let_stmt(i, Some(zero));
        let five = f.lit(5, Ty::uint(32));
        let lj = f.let_stmt(j, Some(five));
        let cond = f.cmp_lit(BinOp::Lt, i, 3);
        let invs = vec![(InvariantKind::Always, f.cmp_lit(BinOp::Le, i, 3))];
        let measure = f.minus(3, i);
        let mut body = vec![f.incr(i)];
        if assign_j {
            let rj = f.rd(j);
            body.push(f.assign(j, rj));
        }
        let lp = f.looped(0, Some(cond), invs, vec![measure], body, false);
        let still = f.cmp_lit(BinOp::Eq, j, 5);
        let a = f.assert(still);
        let r = f.ret(None);
        krate(vec![f.body(vec![li, lj, lp, a, r])])
    };
    let last = |k: &VcCrate| {
        let v = verdicts(&checks_of(k, 1));
        v.chars().last().unwrap()
    };
    assert_eq!(last(&build(false)), 'P');
    assert_eq!(last(&build(true)), 'R');
}

/// The measure must decrease and stay non-negative, at the end of the body
/// and at a `continue`.
#[test]
fn measures_decrease_at_the_end_and_at_continue() {
    let build = |measure_up: bool| {
        let mut f = Fb::new(1, "f", Mode::Exec, Ty::Unit);
        let i = f.let_local("i", Ty::uint(32));
        let zero = f.lit(0, Ty::uint(32));
        let l = f.let_stmt(i, Some(zero));
        let invs = vec![(InvariantKind::Always, f.cmp_lit(BinOp::Le, i, 10))];
        let measure = if measure_up {
            let ri = f.rd(i);
            f.int_of(ri)
        } else {
            f.minus(10, i)
        };
        let below = f.cmp_lit(BinOp::Lt, i, 10);
        let step = f.incr(i);
        let c = f.cont(0);
        let more = f.if_then(below, vec![step, c]);
        let b = f.brk(0);
        let lp = f.looped(0, None, invs, vec![measure], vec![more, b], false);
        let bounded = f.cmp_lit(BinOp::Le, i, 10);
        let a = f.assert(bounded);
        let r = f.ret(None);
        krate(vec![f.body(vec![l, lp, a, r])])
    };
    let checks = checks_of(&build(false), 1);
    assert!(checks.iter().any(|c| matches!(
        c.kind,
        CheckKind::LoopDecreases {
            at_continue: true,
            ..
        }
    )));
    // entry, overflow, continue invariant, continue measure, break, assertion
    assert_eq!(verdicts(&checks), "PPPPPP");
    assert_eq!(verdicts(&checks_of(&build(true), 1)), "PPPRPP");
}

/// A parameter assigned before an isolated loop has an entry value unrelated
/// to its current one in the loop's query, as Verus havocs it after the
/// "pre" snapshot.
#[test]
fn parameters_modified_before_a_loop_lose_their_entry_value() {
    let build = |assign_first: bool| {
        let mut f = Fb::new(1, "f", Mode::Exec, Ty::uint(8));
        let a = f.mut_param("a", Ty::uint(8));
        let (rr, ra) = (f.rd(LocalId(0)), f.rd(a));
        let post = f.cmp(BinOp::Eq, rr, ra);
        f.ensures(post);
        let mut stmts = Vec::new();
        if assign_first {
            let seven = f.lit(7, Ty::uint(8));
            stmts.push(f.assign(a, seven));
        }
        let yes = f.tt(true);
        let zero = f.lit(0, Ty::int());
        let ra = f.rd(a);
        let ret = f.ret(Some(ra));
        let lp = f.looped(
            0,
            None,
            vec![(InvariantKind::Always, yes)],
            vec![zero],
            vec![ret],
            false,
        );
        stmts.push(lp);
        krate(vec![f.body(stmts)])
    };
    assert_eq!(verdicts(&checks_of(&build(false), 1)), "PP");
    assert_eq!(verdicts(&checks_of(&build(true), 1)), "PR");
}

/// Only assignments on the way to a loop count: one in the other branch of
/// an `if` does not (mutable_params.rs `mutation_conditional_cases`).
#[test]
fn parameters_modified_in_another_branch_keep_their_entry_value() {
    let build = |same_branch: bool| {
        let mut f = Fb::new(1, "f", Mode::Exec, Ty::uint(8));
        let a = f.mut_param("a", Ty::uint(8));
        let c = f.param("c", Ty::Bool);
        let (rr, ra) = (f.rd(LocalId(0)), f.rd(a));
        let post = f.cmp(BinOp::Eq, rr, ra);
        f.ensures(post);
        let seven = f.lit(7, Ty::uint(8));
        let assign = f.assign(a, seven);
        let ra = f.rd(a);
        let ret = f.ret(Some(ra));
        let zero = f.lit(0, Ty::int());
        let lp = f.looped(0, None, Vec::new(), vec![zero], vec![ret], false);
        let (then_block, else_block) = if same_branch {
            (Vec::new(), vec![assign, lp])
        } else {
            (vec![assign], vec![lp])
        };
        let rc = f.rd(c);
        let branch = f.stmt(StmtKind::If {
            cond: rc,
            then_block: Block::new(then_block),
            else_block: Block::new(else_block),
        });
        let zero = f.lit(0, Ty::uint(8));
        let r = f.ret(Some(zero));
        krate(vec![f.body(vec![branch, r])])
    };
    let post = |k: &VcCrate| {
        let checks = checks_of(k, 1);
        let at = checks
            .iter()
            .position(|c| matches!(c.kind, CheckKind::Postcondition { .. }))
            .unwrap();
        verdicts(&checks[at..=at])
    };
    assert_eq!(post(&build(false)), "P");
    assert_eq!(post(&build(true)), "R");
}

/// An assignment after a `return` is dropped with the dead code Verus
/// removes, so it does not make the parameter modified
/// (mutable_params.rs `mut_param_with_loops`).
#[test]
fn dead_assignments_do_not_count_as_modifications() {
    let build = |dead: bool| {
        let mut f = Fb::new(1, "f", Mode::Exec, Ty::uint(8));
        let a = f.mut_param("a", Ty::uint(8));
        let (rr, ra) = (f.rd(LocalId(0)), f.rd(a));
        let post = f.cmp(BinOp::Eq, rr, ra);
        f.ensures(post);
        let ra = f.rd(a);
        let ret = f.ret(Some(ra));
        let seven = f.lit(7, Ty::uint(8));
        let assign = f.assign(a, seven);
        let body = if dead {
            vec![ret, assign]
        } else {
            vec![assign, ret]
        };
        let zero = f.lit(0, Ty::int());
        let lp = f.looped(0, None, Vec::new(), vec![zero], body, false);
        krate(vec![f.body(vec![lp])])
    };
    assert_eq!(verdicts(&checks_of(&build(true), 1)), "P");
    assert_eq!(verdicts(&checks_of(&build(false), 1)), "R");
}

/// Verus runs an inner loop's query before its outer loop's.
#[test]
fn inner_loop_queries_come_first() {
    let mut f = Fb::new(1, "f", Mode::Exec, Ty::Unit);
    let yes = f.tt(true);
    let inner_assert = f.assert(yes);
    let r = f.ret(None);
    let zero = f.lit(0, Ty::int());
    let inner = f.looped(
        1,
        None,
        Vec::new(),
        vec![zero],
        vec![inner_assert, r],
        false,
    );
    let yes = f.tt(true);
    let outer_assert = f.assert(yes);
    let zero = f.lit(0, Ty::int());
    let outer = f.looped(
        0,
        None,
        Vec::new(),
        vec![zero],
        vec![outer_assert, inner],
        false,
    );
    let k = krate(vec![f.body(vec![outer])]);
    let checks = checks_of(&k, 1);
    let groups: Vec<QueryGroup> = checks.iter().map(|c| c.group).collect();
    assert!(
        matches!(groups[0], QueryGroup::Loop { index: 1, .. }),
        "{groups:?}"
    );
    assert!(
        matches!(groups[1], QueryGroup::Loop { index: 0, .. }),
        "{groups:?}"
    );
}

/// Without isolation the paths that `break` join after the loop, and the
/// code there knows one of them was taken.
#[test]
fn joined_loops_continue_from_their_breaks() {
    let build = |exit_at: i128| {
        let mut f = Fb::new(1, "f", Mode::Exec, Ty::Unit);
        let i = f.let_local("i", Ty::uint(32));
        let zero = f.lit(0, Ty::uint(32));
        let l = f.let_stmt(i, Some(zero));
        let invs = vec![(InvariantKind::Always, f.cmp_lit(BinOp::Le, i, 10))];
        let measure = f.minus(10, i);
        let at_end = f.cmp_lit(BinOp::Ge, i, exit_at);
        let b = f.brk(0);
        let exit = f.if_then(at_end, vec![b]);
        let step = f.incr(i);
        let lp = f.looped(0, None, invs, vec![measure], vec![exit, step], true);
        let done = f.cmp_lit(BinOp::Eq, i, 10);
        let a = f.assert(done);
        let r = f.ret(None);
        krate(vec![f.body(vec![l, lp, a, r])])
    };
    let last = |k: &VcCrate| verdicts(&checks_of(k, 1)).chars().last().unwrap();
    assert_eq!(last(&build(10)), 'P');
    assert_eq!(last(&build(9)), 'R');
    // A `while` without isolation leaves by its condition as by a `break`.
    let build_while = |bound: i128| {
        let mut f = Fb::new(1, "f", Mode::Exec, Ty::Unit);
        let i = f.let_local("i", Ty::uint(32));
        let zero = f.lit(0, Ty::uint(32));
        let l = f.let_stmt(i, Some(zero));
        let cond = f.cmp_lit(BinOp::Lt, i, 10);
        let invs = vec![(InvariantKind::Always, f.cmp_lit(BinOp::Le, i, bound))];
        let measure = f.minus(11, i);
        let step = f.incr(i);
        let lp = f.looped(0, Some(cond), invs, vec![measure], vec![step], true);
        let done = f.cmp_lit(BinOp::Eq, i, 10);
        let a = f.assert(done);
        let r = f.ret(None);
        krate(vec![f.body(vec![l, lp, a, r])])
    };
    assert_eq!(last(&build_while(10)), 'P');
    assert_eq!(last(&build_while(11)), 'R');
}

/// A loop in proof code, and a `break` of a loop that does not enclose it,
/// are malformed.
#[test]
fn loop_shapes_the_checker_rejects() {
    let mut f = Fb::new(1, "f", Mode::Proof, Ty::Unit);
    let zero = f.lit(0, Ty::int());
    let lp = f.looped(0, None, Vec::new(), vec![zero], Vec::new(), false);
    let r = f.ret(None);
    let k = krate(vec![f.body(vec![lp, r])]);
    let problems = check_crate(&k);
    assert!(
        problems
            .iter()
            .any(|p| p.class == WfClass::Malformed && p.message.contains("a loop in proof code")),
        "{problems:?}"
    );

    let mut f = Fb::new(1, "f", Mode::Exec, Ty::Unit);
    let b = f.brk(3);
    let zero = f.lit(0, Ty::int());
    let lp = f.looped(0, None, Vec::new(), vec![zero], vec![b], false);
    let r = f.ret(None);
    let k = krate(vec![f.body(vec![lp, r])]);
    assert!(check_crate(&k)
        .iter()
        .any(|p| p.message.contains("does not enclose it")));
}

// ----------------------------------------------------------------------
// Termination
// ----------------------------------------------------------------------

/// `(x - n) as nat`, for a `nat` parameter.
fn nat_minus(f: &mut Fb, x: LocalId, n: i128) -> Expr {
    let rx = f.rd(x);
    let ix = f.int_of(rx);
    let lit = f.lit(n, Ty::int());
    let diff = f.bin(BinOp::Sub, ix, lit, Ty::int());
    let span = f.span();
    diff.cast(CastKind::As, Ty::nat(), span)
}

/// `x + n` as `nat`, for a `nat` parameter.
fn nat_plus(f: &mut Fb, x: LocalId, n: i128) -> Expr {
    let rx = f.rd(x);
    let lit = f.lit(n, Ty::nat());
    f.bin(BinOp::Add, rx, lit, Ty::nat())
}

/// Every check of a function and its kind, as `T` for a termination
/// check and `.` for any other, with its verdict.
fn termination_verdicts(checks: &[Check]) -> String {
    checks
        .iter()
        .map(|c| {
            let kind = if matches!(c.kind, CheckKind::Termination { .. }) {
                'T'
            } else {
                '.'
            };
            let verdict = match solve(c) {
                Verdict::Proved { .. } => 'P',
                Verdict::Refuted { .. } => 'R',
                _ => '?',
            };
            format!("{kind}{verdict}")
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn group(members: &[(u64, u32)]) -> RecGroup {
    RecGroup {
        members: members
            .iter()
            .map(|(id, cycle)| (fn_id(*id), *cycle))
            .collect(),
    }
}

/// `proof fn count_down(i: nat) decreases i { if i != 0 { count_down(i - 1) } }`
/// terminates; the twin calls `count_down(i + 1)` (recursion.rs
/// `basic_correctness_stmt`, `stmt_decrease_fail`).
#[test]
fn proof_recursion_decreases_its_measure() {
    let build = |up: bool| {
        let mut f = Fb::new(1, "count_down", Mode::Proof, Ty::Unit);
        let i = f.param("i", Ty::nat());
        let measure = f.rd(i);
        f.decl.decreases.push(measure);
        let arg = if up {
            nat_plus(&mut f, i, 1)
        } else {
            nat_minus(&mut f, i, 1)
        };
        let call = f.call_stmt(fn_id(1), vec![arg], None);
        let cond = f.cmp_lit(BinOp::Ne, i, 0);
        let branch = f.if_then(cond, vec![call]);
        let r = f.ret(None);
        let mut k = krate(vec![f.body(vec![branch, r])]);
        k.rec_groups.push(group(&[(1, 1)]));
        k
    };
    assert_eq!(termination_verdicts(&checks_of(&build(false), 1)), "TP");
    assert_eq!(termination_verdicts(&checks_of(&build(true), 1)), "TR");
}

/// `spec fn sum(i: nat) -> nat decreases i { if i == 0 { 0 } else { i +
/// sum(i - 1) } }` terminates; the twin's recursive call is `sum(i)`
/// (recursion.rs `basic_correctness_expr`, `expr_decrease_fail_3`).
#[test]
fn spec_recursion_decreases_its_measure() {
    let build = |same: bool| {
        let mut f = Fb::new(1, "sum", Mode::Spec, Ty::nat());
        let i = f.param("i", Ty::nat());
        let measure = f.rd(i);
        f.decl.decreases.push(measure);
        let arg = if same {
            f.rd(i)
        } else {
            nat_minus(&mut f, i, 1)
        };
        let rec = f.call(fn_id(1), vec![arg], Ty::nat());
        let ri = f.rd(i);
        let sum = f.bin(BinOp::Add, ri, rec, Ty::nat());
        let zero = f.lit(0, Ty::nat());
        let cond = f.cmp_lit(BinOp::Eq, i, 0);
        let span = f.span();
        let body = Expr::new(
            Ty::nat(),
            span,
            ExprKind::If {
                cond: Box::new(cond),
                then_expr: Box::new(zero),
                else_expr: Box::new(sum),
            },
        );
        let mut k = krate(vec![f.spec_body(body)]);
        k.rec_groups.push(group(&[(1, 1)]));
        k
    };
    assert_eq!(termination_verdicts(&checks_of(&build(false), 1)), "TP");
    assert_eq!(termination_verdicts(&checks_of(&build(true), 1)), "TR");
}

/// `count_down_a` and `count_down_b` call each other, a cycle of length 2:
/// a call unfolds twice, so `count_down_a(1) == 1` is proved and
/// `count_down_a(2) == 2` is not (recursion.rs
/// `mutually_recursive_expressions_insufficient_fuel`). The twin of the
/// first is the second.
#[test]
fn fuel_unfolds_one_cycle() {
    let count_down = |id: u64, other: u64, name: &str| {
        let mut f = Fb::new(id, name, Mode::Spec, Ty::nat());
        let i = f.param("i", Ty::nat());
        let measure = f.rd(i);
        f.decl.decreases.push(measure);
        let arg = nat_minus(&mut f, i, 1);
        let rec = f.call(fn_id(other), vec![arg], Ty::nat());
        let one = f.lit(1, Ty::nat());
        let sum = f.bin(BinOp::Add, one, rec, Ty::nat());
        let zero = f.lit(0, Ty::nat());
        let cond = f.cmp_lit(BinOp::Eq, i, 0);
        let span = f.span();
        let body = Expr::new(
            Ty::nat(),
            span,
            ExprKind::If {
                cond: Box::new(cond),
                then_expr: Box::new(zero),
                else_expr: Box::new(sum),
            },
        );
        f.spec_body(body)
    };
    let build = |n: i128| {
        let mut t = Fb::new(3, "t", Mode::Proof, Ty::Unit);
        let arg = t.lit(n, Ty::nat());
        let call = t.call(fn_id(1), vec![arg], Ty::nat());
        let want = t.lit(n, Ty::nat());
        let goal = t.cmp(BinOp::Eq, call, want);
        let a = t.assert(goal);
        let r = t.ret(None);
        let mut k = krate(vec![
            count_down(1, 2, "count_down_a"),
            count_down(2, 1, "count_down_b"),
            t.body(vec![a, r]),
        ]);
        k.rec_groups.push(group(&[(1, 2), (2, 2)]));
        k
    };
    assert_eq!(termination_verdicts(&checks_of(&build(1), 3)), ".P");
    assert_eq!(termination_verdicts(&checks_of(&build(2), 3)), ".R");
    // Both members terminate.
    assert_eq!(termination_verdicts(&checks_of(&build(1), 1)), "TP");
    assert_eq!(termination_verdicts(&checks_of(&build(1), 2)), "TP");
}

/// A function on a cycle of length 1 unfolds once with the default fuel;
/// `reveal_with_fuel(f, 2)` unfolds it twice (recursion.rs
/// `mutually_recursive_expressions_insufficient_fuel_short_cycle`).
#[test]
fn reveal_with_fuel_unfolds_further() {
    let build = |fuel: Option<u32>, branch_fuel: Option<(u32, u32)>| {
        let mut f = Fb::new(1, "f", Mode::Spec, Ty::nat());
        let i = f.param("i", Ty::nat());
        let measure = f.rd(i);
        f.decl.decreases.push(measure);
        let arg = nat_minus(&mut f, i, 1);
        let rec = f.call(fn_id(1), vec![arg], Ty::nat());
        let one = f.lit(1, Ty::nat());
        let sum = f.bin(BinOp::Add, one, rec, Ty::nat());
        let zero = f.lit(0, Ty::nat());
        let cond = f.cmp_lit(BinOp::Eq, i, 0);
        let span = f.span();
        let body = Expr::new(
            Ty::nat(),
            span,
            ExprKind::If {
                cond: Box::new(cond),
                then_expr: Box::new(zero),
                else_expr: Box::new(sum),
            },
        );
        let f = f.spec_body(body);
        let mut t = Fb::new(2, "t", Mode::Proof, Ty::Unit);
        let mut stmts = Vec::new();
        if let Some(fuel) = fuel {
            stmts.push(t.stmt(StmtKind::Reveal {
                callee: fn_id(1),
                fuel: Some(fuel),
            }));
        }
        if let Some((then_fuel, else_fuel)) = branch_fuel {
            let b = t.param("b", Ty::Bool);
            let cond = t.rd(b);
            let then_reveal = t.stmt(StmtKind::Reveal {
                callee: fn_id(1),
                fuel: Some(then_fuel),
            });
            let else_reveal = t.stmt(StmtKind::Reveal {
                callee: fn_id(1),
                fuel: Some(else_fuel),
            });
            stmts.push(t.stmt(StmtKind::If {
                cond,
                then_block: Block::new(vec![then_reveal]),
                else_block: Block::new(vec![else_reveal]),
            }));
        }
        let arg = t.lit(1, Ty::nat());
        let call = t.call(fn_id(1), vec![arg], Ty::nat());
        let want = t.lit(1, Ty::nat());
        let goal = t.cmp(BinOp::Eq, call, want);
        stmts.push(t.assert(goal));
        stmts.push(t.ret(None));
        let mut k = krate(vec![f, t.body(stmts)]);
        k.rec_groups.push(group(&[(1, 1)]));
        k
    };
    assert_eq!(
        termination_verdicts(&checks_of(&build(None, None), 2)),
        ".R"
    );
    assert_eq!(
        termination_verdicts(&checks_of(&build(Some(2), None), 2)),
        ".P"
    );
    for (fuels, expected) in [((2, 2), ".P"), ((2, 1), ".R"), ((1, 2), ".R")] {
        assert_eq!(
            termination_verdicts(&checks_of(&build(None, Some(fuels)), 2)),
            expected
        );
    }
}

/// A lexicographic measure: `dec2(j, k) decreases j, k` may call
/// `dec2(j, k - 1)` but not `dec2(j, k)`; a callee with fewer components
/// than the caller must decrease within them (recursion.rs
/// `multidecrease1`, `multidecrease1_fail1`).
#[test]
fn lexicographic_measures() {
    let build = |same: bool| {
        let mut f = Fb::new(1, "dec2", Mode::Proof, Ty::Unit);
        let j = f.param("j", Ty::nat());
        let k = f.param("k", Ty::nat());
        let (mj, mk) = (f.rd(j), f.rd(k));
        f.decl.decreases.extend([mj, mk]);
        let rj = f.rd(j);
        let arg = if same {
            f.rd(k)
        } else {
            nat_minus(&mut f, k, 1)
        };
        let call = f.call_stmt(fn_id(1), vec![rj, arg], None);
        let cond = f.cmp_lit(BinOp::Gt, k, 0);
        let branch = f.if_then(cond, vec![call]);
        let r = f.ret(None);
        let mut krate = krate(vec![f.body(vec![branch, r])]);
        krate.rec_groups.push(group(&[(1, 1)]));
        krate
    };
    assert_eq!(termination_verdicts(&checks_of(&build(false), 1)), "TP");
    assert_eq!(termination_verdicts(&checks_of(&build(true), 1)), "TR");
}

/// `spec fn f(i: int) -> int decreases i when i >= 0`: the condition is
/// assumed by the termination check and guards the definition (recursion.rs
/// `proof_decreases_when_ok`, `proof_decreases_when_fail`). The twins drop
/// the condition, and assert the definition where it does not hold.
#[test]
fn when_guards_termination_and_definition() {
    let build = |when: bool, at: i128| {
        let mut f = Fb::new(1, "f", Mode::Spec, Ty::int());
        let i = f.param("i", Ty::int());
        let measure = f.rd(i);
        f.decl.decreases.push(measure);
        if when {
            let cond = f.cmp_lit(BinOp::Ge, i, 0);
            f.decl.decreases_when = Some(cond);
        }
        let ri = f.rd(i);
        let one = f.lit(1, Ty::int());
        let arg = f.bin(BinOp::Sub, ri, one, Ty::int());
        let rec = f.call(fn_id(1), vec![arg], Ty::int());
        let ri = f.rd(i);
        let sum = f.bin(BinOp::Add, ri, rec, Ty::int());
        let zero = f.lit(0, Ty::int());
        let cond = f.cmp_lit(BinOp::Eq, i, 0);
        let span = f.span();
        let body = Expr::new(
            Ty::int(),
            span,
            ExprKind::If {
                cond: Box::new(cond),
                then_expr: Box::new(zero),
                else_expr: Box::new(sum),
            },
        );
        let f = f.spec_body(body);
        // assert(f(at) == at + f(at - 1))
        let mut t = Fb::new(2, "t", Mode::Proof, Ty::Unit);
        let a = t.lit(at, Ty::int());
        let lhs = t.call(fn_id(1), vec![a], Ty::int());
        let a1 = t.lit(at - 1, Ty::int());
        let inner = t.call(fn_id(1), vec![a1], Ty::int());
        let a = t.lit(at, Ty::int());
        let rhs = t.bin(BinOp::Add, a, inner, Ty::int());
        let goal = t.cmp(BinOp::Eq, lhs, rhs);
        let assert = t.assert(goal);
        let r = t.ret(None);
        let mut k = krate(vec![f, t.body(vec![assert, r])]);
        k.rec_groups.push(group(&[(1, 1)]));
        k
    };
    assert_eq!(termination_verdicts(&checks_of(&build(true, 2), 1)), "TP");
    assert_eq!(termination_verdicts(&checks_of(&build(false, 2), 1)), "TR");
    assert_eq!(termination_verdicts(&checks_of(&build(true, 2), 2)), ".P");
    assert_eq!(termination_verdicts(&checks_of(&build(true, -1), 2)), ".R");
}

/// An exec function without a measure that allows none has no termination
/// checks; with a measure it has them (exec_termination.rs).
#[test]
fn exec_allows_no_decreases() {
    let build = |measure: bool| {
        let mut f = Fb::new(1, "e", Mode::Exec, Ty::Unit);
        let i = f.param("i", Ty::uint(64));
        f.decl.attrs.exec_allows_no_decreases = true;
        if measure {
            let ri = f.rd(i);
            let m = f.int_of(ri);
            f.decl.decreases.push(m);
        }
        let ri = f.rd(i);
        let call = f.call_stmt(fn_id(1), vec![ri], None);
        let r = f.ret(None);
        let mut k = krate(vec![f.body(vec![call, r])]);
        k.rec_groups.push(group(&[(1, 1)]));
        k
    };
    assert_eq!(termination_verdicts(&checks_of(&build(false), 1)), "");
    assert_eq!(termination_verdicts(&checks_of(&build(true), 1)), "TR");
}

/// A cycle of calls that no group covers is refused; so is a member of a
/// group without a measure.
#[test]
fn undeclared_recursion_is_refused() {
    let build = |declared: bool| {
        let mut f = Fb::new(1, "f", Mode::Proof, Ty::Unit);
        let i = f.param("i", Ty::nat());
        let ri = f.rd(i);
        let call = f.call_stmt(fn_id(1), vec![ri], None);
        let r = f.ret(None);
        let mut k = krate(vec![f.body(vec![call, r])]);
        if declared {
            k.rec_groups.push(group(&[(1, 1)]));
        }
        k
    };
    assert_eq!(refusal_tag(&build(false), 1), "recursion");
    assert_eq!(refusal_tag(&build(true), 1), "recursion-without-decreases");
}

// ----------------------------------------------------------------------
// Quantifiers and choices
// ----------------------------------------------------------------------

const P: u64 = 1;
const Q: u64 = 2;
const T: u64 = 3;

/// `spec fn <name>(x: int) -> bool;`, uninterpreted.
fn predicate(id: u64, name: &str) -> FnDecl {
    let mut f = Fb::new(id, name, Mode::Spec, Ty::Bool);
    f.param("x", Ty::int());
    f.decl
}

impl Fb {
    fn bound(&mut self, name: &str, ty: Ty) -> LocalId {
        self.add_local(name, ty, false, LocalKind::Bound)
    }

    /// `pred(arg)` for one of the predicates `p` and `q`.
    fn pred(&mut self, pred: u64, arg: Expr) -> Expr {
        self.call(fn_id(pred), vec![arg], Ty::Bool)
    }

    /// `pred(x)` for a local `x`.
    fn pred_of(&mut self, pred: u64, x: LocalId) -> Expr {
        let rx = self.rd(x);
        self.pred(pred, rx)
    }

    fn quant(
        &mut self,
        kind: QuantKind,
        vars: &[LocalId],
        triggers: Vec<Vec<Expr>>,
        body: Expr,
    ) -> Expr {
        let vars = vars
            .iter()
            .map(|v| (*v, self.decl.locals[v.index()].ty.clone()))
            .collect();
        let span = self.span();
        Expr::new(
            Ty::Bool,
            span,
            ExprKind::Quant {
                kind,
                vars,
                triggers,
                body: Box::new(body),
            },
        )
    }

    /// `choose|x| cond`, with the triggers of `exists|x| cond`.
    fn choose(&mut self, x: LocalId, triggers: Vec<Vec<Expr>>, cond: Expr) -> Expr {
        let ty = self.decl.locals[x.index()].ty.clone();
        let result = self.rd(x);
        let span = self.span();
        Expr::new(
            ty.clone(),
            span,
            ExprKind::Choose {
                vars: vec![(x, ty)],
                triggers,
                cond: Box::new(cond),
                result: Box::new(result),
            },
        )
    }
}

/// `proof fn t() requires <pres> { assert(<goal>); }` beside `spec fn p(x:
/// int) -> bool;` and `spec fn q(x: int) -> bool;`.
fn quant_crate(build: impl FnOnce(&mut Fb) -> (Vec<Expr>, Expr)) -> VcCrate {
    let mut t = Fb::new(T, "t", Mode::Proof, Ty::Unit);
    let (pres, goal) = build(&mut t);
    for pre in pres {
        t.requires(pre);
    }
    let a = t.assert(goal);
    let r = t.ret(None);
    krate(vec![
        predicate(P, "p"),
        predicate(Q, "q"),
        t.body(vec![a, r]),
    ])
}

/// `requires forall|x: int| #[trigger] p(x)` proves `p(3)`; the twin's
/// `exists` does not.
#[test]
fn a_forall_fact_is_instantiated_and_an_exists_fact_is_not() {
    let build = |kind: QuantKind| {
        quant_crate(|t| {
            let x = t.bound("x", Ty::int());
            let trigger = t.pred_of(P, x);
            let body = t.pred_of(P, x);
            let pre = t.quant(kind, &[x], vec![vec![trigger]], body);
            let three = t.lit(3, Ty::int());
            let goal = t.pred(P, three);
            (vec![pre], goal)
        })
    };
    assert_eq!(verdicts(&checks_of(&build(QuantKind::Forall), T)), "P");
    assert_eq!(verdicts(&checks_of(&build(QuantKind::Exists), T)), "R");
}

/// `requires forall|x: int| p(x) && q(x)` proves `q(3)` with the trigger
/// `q(x)`, which the goal's `q(3)` matches. With the trigger `p(x)` no term
/// of the query matches, so there is no instance, as in Z3 with
/// E-matching only (how Verus runs it), although the goal follows in
/// first-order logic.
#[test]
fn only_terms_that_match_a_trigger_are_instances() {
    let build = |trigger_pred: u64| {
        quant_crate(|t| {
            let x = t.bound("x", Ty::int());
            let trigger = t.pred_of(trigger_pred, x);
            let (px, qx) = (t.pred_of(P, x), t.pred_of(Q, x));
            let body = t.bin(BinOp::And, px, qx, Ty::Bool);
            let pre = t.quant(QuantKind::Forall, &[x], vec![vec![trigger]], body);
            let three = t.lit(3, Ty::int());
            let goal = t.pred(Q, three);
            (vec![pre], goal)
        })
    };
    assert_eq!(verdicts(&checks_of(&build(Q), T)), "P");
    assert_ne!(verdicts(&checks_of(&build(P), T)), "P");
}

/// `requires forall|x: int| #[trigger] p(x) ==> q(x), p(3)` proves `q(3)`:
/// the trigger matches the hypothesis's `p(3)`. With `p(4)` the instance
/// is at 4 and says nothing about `q(3)`.
#[test]
fn a_hypothesis_term_matches_a_trigger() {
    let build = |known: i128| {
        quant_crate(|t| {
            let x = t.bound("x", Ty::int());
            let trigger = t.pred_of(P, x);
            let (px, qx) = (t.pred_of(P, x), t.pred_of(Q, x));
            let body = t.bin(BinOp::Implies, px, qx, Ty::Bool);
            let rule = t.quant(QuantKind::Forall, &[x], vec![vec![trigger]], body);
            let n = t.lit(known, Ty::int());
            let fact = t.pred(P, n);
            let three = t.lit(3, Ty::int());
            let goal = t.pred(Q, three);
            (vec![rule, fact], goal)
        })
    };
    assert_eq!(verdicts(&checks_of(&build(3), T)), "P");
    assert_eq!(verdicts(&checks_of(&build(4), T)), "R");
}

/// `assert(exists|x: int| #[trigger] p(x) && x == 3)` holds given `p(3)`:
/// the witness is the hypothesis's term. Given `p(4)` the only witness
/// tried is 4, which fails, and nothing else proves it.
#[test]
fn an_exists_goal_is_proved_by_a_matching_witness() {
    let build = |known: i128| {
        quant_crate(|t| {
            let n = t.lit(known, Ty::int());
            let fact = t.pred(P, n);
            let x = t.bound("x", Ty::int());
            let trigger = t.pred_of(P, x);
            let px = t.pred_of(P, x);
            let (rx, three) = (t.rd(x), t.lit(3, Ty::int()));
            let is_three = t.cmp(BinOp::Eq, rx, three);
            let body = t.bin(BinOp::And, px, is_three, Ty::Bool);
            let goal = t.quant(QuantKind::Exists, &[x], vec![vec![trigger]], body);
            (vec![fact], goal)
        })
    };
    assert_eq!(verdicts(&checks_of(&build(3), T)), "P");
    assert_eq!(verdicts(&checks_of(&build(4), T)), "R");
}

/// `choose|x: int| p(x)` satisfies `p` when something does: `requires
/// exists|y: int| #[trigger] p(y)` proves `p(choose|x: int| p(x))`. The
/// twin requires a `q` and proves nothing about `p`.
#[test]
fn a_choice_satisfies_its_condition_when_something_does() {
    let build = |known: u64| {
        quant_crate(|t| {
            let y = t.bound("y", Ty::int());
            let trigger = t.pred_of(known, y);
            let body = t.pred_of(known, y);
            let pre = t.quant(QuantKind::Exists, &[y], vec![vec![trigger]], body);
            let x = t.bound("x", Ty::int());
            let trigger = t.pred_of(P, x);
            let cond = t.pred_of(P, x);
            let chosen = t.choose(x, vec![vec![trigger]], cond);
            let goal = t.pred(P, chosen);
            (vec![pre], goal)
        })
    };
    assert_eq!(verdicts(&checks_of(&build(P), T)), "P");
    assert_eq!(verdicts(&checks_of(&build(Q), T)), "R");
}

/// A quantifier's variables are bound locals of their types, and it has
/// trigger groups that each mention every variable; anything else is
/// malformed.
#[test]
fn quantifier_binders_and_triggers_are_well_formed() {
    #[derive(Clone, Copy)]
    enum Flaw {
        None,
        NoTriggers,
        ParamVar,
        UncoveredVar,
    }
    let build = |flaw: Flaw| {
        quant_crate(|t| {
            let x = match flaw {
                Flaw::ParamVar => t.param("x", Ty::int()),
                _ => t.bound("x", Ty::int()),
            };
            let y = t.bound("y", Ty::int());
            let trigger = match flaw {
                Flaw::UncoveredVar => t.pred_of(P, x),
                _ => {
                    let (rx, ry) = (t.rd(x), t.rd(y));
                    let sum = t.bin(BinOp::Add, rx, ry, Ty::int());
                    t.pred(P, sum)
                }
            };
            let triggers = match flaw {
                Flaw::NoTriggers => Vec::new(),
                _ => vec![vec![trigger]],
            };
            let (px, qy) = (t.pred_of(P, x), t.pred_of(Q, y));
            let body = t.bin(BinOp::Or, px, qy, Ty::Bool);
            let pre = t.quant(QuantKind::Forall, &[x, y], triggers, body);
            let tt = t.tt(true);
            (vec![pre], tt)
        })
    };
    let messages = |flaw: Flaw| -> Vec<String> {
        check_crate(&build(flaw))
            .into_iter()
            .filter(|p| p.class == WfClass::Malformed)
            .map(|p| p.message)
            .collect()
    };
    assert_eq!(messages(Flaw::None), Vec::<String>::new());
    let expect = [
        (Flaw::NoTriggers, "a quantifier without triggers"),
        (
            Flaw::ParamVar,
            "a quantifier variable that is not a bound local",
        ),
        (
            Flaw::UncoveredVar,
            "a trigger group that does not mention every variable",
        ),
    ];
    for (flaw, want) in expect {
        let found = messages(flaw);
        assert!(
            found.iter().any(|m| m.contains(want)),
            "expected `{want}`, got {found:?}"
        );
    }
}
