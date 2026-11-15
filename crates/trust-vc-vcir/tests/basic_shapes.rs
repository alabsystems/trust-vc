//! VcIR built by hand for functions from upstream Verus `basic.rs`, checked by
//! `check_crate`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The accepted crates show the types can express what the reader will
//! produce for basic.rs. Each rejected crate differs from an accepted shape in
//! one place and must be rejected with the class (and, for user errors,
//! Verus's message) given.

use trust_vc_vcir::wf::{
    msg_not_mutable, MSG_ASSIGN_IN_PURE, MSG_CALL_PROOF_FROM_EXEC, MSG_DUPLICATE_NOTE,
    MSG_MUT_SPEC_PARAM,
};
use trust_vc_vcir::{
    check_crate, AdtDecl, AdtId, AdtKind, BinOp, Block, Body, CastKind, Clause, ClauseAttrs,
    DefHash, Expr, ExprKind, FieldDecl, FnAttrs, FnDecl, FnId, FnRole, IntLit, IntRange, LocalDecl,
    LocalId, LocalKind, Mode, Place, SiteId, SpanId, Stmt, StmtKind, Ty, VariantDecl, VcCrate,
    WfClass, WfError,
};

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
        let decl = FnDecl {
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
            attrs: FnAttrs::default(),
            body: Body::None,
        };
        Self {
            decl,
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

    fn add_local(
        &mut self,
        name: &str,
        ty: Ty,
        mode: Mode,
        mutable: bool,
        kind: LocalKind,
    ) -> LocalId {
        let span = self.span();
        let id = LocalId(u32::try_from(self.decl.locals.len()).unwrap());
        self.decl.locals.push(LocalDecl {
            name: name.to_string(),
            ty,
            mode,
            mutable,
            kind,
            span,
        });
        id
    }

    fn param(&mut self, name: &str, ty: Ty, mutable: bool) -> LocalId {
        let mode = if self.decl.mode == Mode::Exec {
            Mode::Exec
        } else {
            Mode::Spec
        };
        let id = self.add_local(name, ty, mode, mutable, LocalKind::Param);
        self.decl.params.push(id);
        id
    }

    fn let_local(&mut self, name: &str, ty: Ty, mutable: bool) -> LocalId {
        let mode = if self.decl.mode == Mode::Exec {
            Mode::Exec
        } else {
            Mode::Spec
        };
        self.add_local(name, ty, mode, mutable, LocalKind::Let)
    }

    fn bound(&mut self, name: &str, ty: Ty) -> LocalId {
        self.add_local(name, ty, Mode::Spec, false, LocalKind::Bound)
    }

    fn ty_of(&self, local: LocalId) -> Ty {
        self.decl.locals[local.index()].ty.clone()
    }

    fn rd(&mut self, local: LocalId) -> Expr {
        let ty = self.ty_of(local);
        let span = self.span();
        Expr::read(Place::local(local), ty, span)
    }

    fn lit(&mut self, value: i128, ty: Ty) -> Expr {
        let span = self.span();
        Expr::int_lit(value, ty, span)
    }

    fn bool_lit(&mut self, value: bool) -> Expr {
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

    fn assign(&mut self, place: Place, value: Expr) -> Stmt {
        self.stmt(StmtKind::Assign { place, value })
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

/// A joined query may unfold a definition only when every continuing
/// branch revealed it. A returning sibling imposes no fuel requirement.
#[test]
fn reveal_visibility_at_branch_join() {
    use trust_vc_vcir::vcgen::{generate, term::Term, FnVcs};

    for (reveal_else, return_else, condition, dead_then, expected_visible) in [
        (true, false, None, false, true),
        (false, false, None, false, false),
        (false, true, None, false, true),
        (false, false, Some(true), false, true),
        (false, false, Some(false), false, false),
        (false, false, None, true, false),
    ] {
        let mut one = Fb::new(1, "one", Mode::Spec, Ty::int());
        one.decl.attrs.opaque = true;
        let value = one.lit(1, Ty::int());
        let one = one.spec_body(value);
        let mut t = Fb::new(2, "t", Mode::Proof, Ty::Unit);
        let b = t.param("b", Ty::Bool, false);
        let reveal = t.stmt(StmtKind::Reveal {
            callee: fn_id(1),
            fuel: None,
        });
        let else_stmts = if return_else {
            vec![t.ret(None)]
        } else if reveal_else {
            vec![reveal.clone()]
        } else {
            vec![]
        };
        let cond = match condition {
            Some(value) => t.bool_lit(value),
            None => t.rd(b),
        };
        let mut then_stmts = vec![reveal];
        if dead_then {
            // The reader lowers an assert-by proof to an arbitrary branch
            // ending unreachable. Its fuel cannot escape the proof.
            then_stmts.push(t.stmt(StmtKind::Unreachable));
        }
        let branch = t.stmt(StmtKind::If {
            cond,
            then_block: Block::new(then_stmts),
            else_block: Block::new(else_stmts),
        });
        let call = t.call(fn_id(1), vec![], Ty::int());
        let value = t.lit(1, Ty::int());
        let goal = t.cmp(BinOp::Eq, call, value);
        let assertion = t.assert(goal);
        let ret = t.ret(None);
        let krate = krate(vec![one, t.body(vec![branch, assertion, ret])]);
        assert_well_formed(&krate);
        let vcs = generate(&krate);
        let Some(FnVcs::Checks(checks)) = vcs.get(fn_id(2)) else {
            panic!("expected generated checks, got {vcs:?}");
        };
        assert_eq!(checks.len(), 1);
        assert_eq!(checks[0].query.goal == Term::Bool(true), expected_visible);
    }
}

#[track_caller]
fn assert_well_formed(krate: &VcCrate) {
    let errors = check_crate(krate);
    assert!(errors.is_empty(), "expected no problems, got {errors:#?}");
}

#[track_caller]
fn assert_user_error(errors: &[WfError], message: &str) {
    assert!(
        errors
            .iter()
            .any(|error| error.class == WfClass::User && error.message == message),
        "expected user error {message:?}, got {errors:#?}"
    );
}

#[track_caller]
fn assert_malformed(errors: &[WfError], needle: &str) {
    assert!(
        errors
            .iter()
            .any(|error| error.class == WfClass::Malformed && error.message.contains(needle)),
        "expected a malformed-IR problem mentioning {needle:?}, got {errors:#?}"
    );
}

// ----------------------------------------------------------------------
// basic.rs shapes that must be accepted
// ----------------------------------------------------------------------

/// `spec fn f1(i: int, j: int) -> bool { i <= j }` and friends from
/// `test_spec_fn`, plus the exec function that uses them.
fn test_spec_fn_crate() -> VcCrate {
    let mut f1 = Fb::new(1, "f1", Mode::Spec, Ty::Bool);
    let i = f1.param("i", Ty::int(), false);
    let j = f1.param("j", Ty::int(), false);
    let (ri, rj) = (f1.rd(i), f1.rd(j));
    let body = f1.cmp(BinOp::Le, ri, rj);
    let f1 = f1.spec_body(body);

    // spec fn f2(i: int, j: int) -> bool { let x = i; let y = j; x < y }
    let mut f2 = Fb::new(2, "f2", Mode::Spec, Ty::Bool);
    let i = f2.param("i", Ty::int(), false);
    let j = f2.param("j", Ty::int(), false);
    let x = f2.bound("x", Ty::int());
    let y = f2.bound("y", Ty::int());
    let (rx, ry, ri, rj) = (f2.rd(x), f2.rd(y), f2.rd(i), f2.rd(j));
    let lt = f2.cmp(BinOp::Lt, rx, ry);
    let span = f2.span();
    let inner = Expr::new(
        Ty::Bool,
        span,
        ExprKind::Let {
            local: y,
            value: Box::new(rj),
            body: Box::new(lt),
        },
    );
    let span = f2.span();
    let outer = Expr::new(
        Ty::Bool,
        span,
        ExprKind::Let {
            local: x,
            value: Box::new(ri),
            body: Box::new(inner),
        },
    );
    let f2 = f2.spec_body(outer);

    // #[verifier(opaque)] spec fn f3(i: int, j: int) -> bool { f1(j, i) }
    let mut f3 = Fb::new(3, "f3", Mode::Spec, Ty::Bool);
    f3.decl.attrs.opaque = true;
    let i = f3.param("i", Ty::int(), false);
    let j = f3.param("j", Ty::int(), false);
    let (rj, ri) = (f3.rd(j), f3.rd(i));
    let body = f3.call(fn_id(1), vec![rj, ri], Ty::Bool);
    let f3 = f3.spec_body(body);

    // fn test_spec_fn(a: int, b: int) { hide(f2); assume(f2(a, b));
    //   proof { reveal(f2); } assert(f1(a, b)); proof { reveal(f3); }
    //   assert(f3(b, a)); assert(f3(a, b)); }
    let mut t = Fb::new(4, "test_spec_fn", Mode::Exec, Ty::Unit);
    let a = t.param("a", Ty::int(), false);
    let b = t.param("b", Ty::int(), false);
    let hide = t.stmt(StmtKind::Hide { callee: fn_id(2) });
    let (ra, rb) = (t.rd(a), t.rd(b));
    let f2ab = t.call(fn_id(2), vec![ra, rb], Ty::Bool);
    let assume = t.assume(f2ab);
    let reveal_f2 = t.stmt(StmtKind::Reveal {
        callee: fn_id(2),
        fuel: None,
    });
    let ghost1 = t.stmt(StmtKind::Ghost(Block::new(vec![reveal_f2])));
    let (ra, rb) = (t.rd(a), t.rd(b));
    let f1ab = t.call(fn_id(1), vec![ra, rb], Ty::Bool);
    let assert1 = t.assert(f1ab);
    let reveal_f3 = t.stmt(StmtKind::Reveal {
        callee: fn_id(3),
        fuel: None,
    });
    let ghost2 = t.stmt(StmtKind::Ghost(Block::new(vec![reveal_f3])));
    let (rb, ra) = (t.rd(b), t.rd(a));
    let f3ba = t.call(fn_id(3), vec![rb, ra], Ty::Bool);
    let assert2 = t.assert(f3ba);
    let (ra, rb) = (t.rd(a), t.rd(b));
    let f3ab = t.call(fn_id(3), vec![ra, rb], Ty::Bool);
    let assert3 = t.assert(f3ab);
    let ret = t.ret(None);
    let t = t.body(vec![
        hide, assume, ghost1, assert1, ghost2, assert2, assert3, ret,
    ]);

    krate(vec![f1, f2, f3, t])
}

#[test]
fn test_spec_fn_is_well_formed() {
    assert_well_formed(&test_spec_fn_crate());
}

/// `proof fn test_requires1(a: int, b: int, c: int) requires a <= b,
/// #![verifier::proof_note("Test label #1")] b <= c { assert(a <= c); }` and
/// `test_requires2`, which calls it twice.
fn test_requires_crate(notes_on_second_clause: &[&str]) -> VcCrate {
    let mut r1 = Fb::new(10, "test_requires1", Mode::Proof, Ty::Unit);
    let a = r1.param("a", Ty::int(), false);
    let b = r1.param("b", Ty::int(), false);
    let c = r1.param("c", Ty::int(), false);
    let (ra, rb) = (r1.rd(a), r1.rd(b));
    let ab = r1.cmp(BinOp::Le, ra, rb);
    let (rb, rc) = (r1.rd(b), r1.rd(c));
    let bc = r1.cmp(BinOp::Le, rb, rc);
    let first = r1.clause(ab);
    let mut second = r1.clause(bc);
    second.attrs.proof_notes = notes_on_second_clause
        .iter()
        .map(|s| s.to_string())
        .collect();
    r1.decl.requires = vec![first, second];
    let (ra, rc) = (r1.rd(a), r1.rd(c));
    let ac = r1.cmp(BinOp::Le, ra, rc);
    let assert = r1.assert(ac);
    let ret = r1.ret(None);
    let r1 = r1.body(vec![assert, ret]);

    let mut r2 = Fb::new(11, "test_requires2", Mode::Proof, Ty::Unit);
    let a = r2.param("a", Ty::int(), false);
    let b = r2.param("b", Ty::int(), false);
    let c = r2.param("c", Ty::int(), false);
    let double = |fb: &mut Fb, local: LocalId| {
        let (l, r) = (fb.rd(local), fb.rd(local));
        fb.bin(BinOp::Add, l, r, Ty::int())
    };
    let args1 = vec![double(&mut r2, a), double(&mut r2, b), double(&mut r2, c)];
    let call1 = r2.call_stmt(fn_id(10), args1, None);
    let (ra, rc) = (r2.rd(a), r2.rd(c));
    let a_plus_c = r2.bin(BinOp::Add, ra, rc, Ty::int());
    let args2 = vec![double(&mut r2, a), double(&mut r2, b), a_plus_c];
    let call2 = r2.call_stmt(fn_id(10), args2, None);
    let ret = r2.ret(None);
    let r2 = r2.body(vec![call1, call2, ret]);
    krate(vec![r1, r2])
}

#[test]
fn test_requires_is_well_formed() {
    assert_well_formed(&test_requires_crate(&["Test label #1"]));
}

#[test]
fn duplicate_proof_note_is_the_verus_error() {
    let errors = check_crate(&test_requires_crate(&["Property 732", "Property 451"]));
    assert_user_error(&errors, MSG_DUPLICATE_NOTE);
}

/// `fn example(x: u64, y: u64) -> (z: u64) requires x == y { x + y }` and
/// `fn caller() { let _ = example(1, 2); }`.
fn exec_call_crate() -> VcCrate {
    let mut ex = Fb::new(20, "example", Mode::Exec, Ty::uint(64));
    let x = ex.param("x", Ty::uint(64), false);
    let y = ex.param("y", Ty::uint(64), false);
    let (rx, ry) = (ex.rd(x), ex.rd(y));
    let eq = ex.cmp(BinOp::Eq, rx, ry);
    let mut clause = ex.clause(eq);
    clause.attrs.proof_notes = vec!["Property 732".to_string()];
    ex.decl.requires = vec![clause];
    let (rx, ry) = (ex.rd(x), ex.rd(y));
    let sum = ex.checked(BinOp::Add, rx, ry);
    let ret = ex.ret(Some(sum));
    let ex = ex.body(vec![ret]);

    let mut caller = Fb::new(21, "caller", Mode::Exec, Ty::Unit);
    let tmp = caller.add_local("_", Ty::uint(64), Mode::Exec, false, LocalKind::Temp);
    let decl_tmp = caller.stmt(StmtKind::Let {
        local: tmp,
        init: None,
    });
    let one = caller.lit(1, Ty::uint(64));
    let two = caller.lit(2, Ty::uint(64));
    let call = caller.call_stmt(fn_id(20), vec![one, two], Some(Place::local(tmp)));
    let ret = caller.ret(None);
    let caller = caller.body(vec![decl_tmp, call, ret]);
    krate(vec![ex, caller])
}

#[test]
fn exec_call_with_checked_arithmetic_is_well_formed() {
    assert_well_formed(&exec_call_crate());
}

/// `fn test1(y: &mut u32) { let mut x: i32 = 1; x += 2; assert(x == 3 as
/// i32); *y /= 2; assert(*y == *old(y) / 2); }` and `proof fn test2a() { let
/// mut x: u8 = 200; x = (x + 100u8) as u8; assert(x < 256); }` from
/// `test_compound_assign`.
fn compound_assign_crate() -> VcCrate {
    let mut t1 = Fb::new(30, "test1", Mode::Exec, Ty::Unit);
    let y_ty = Ty::Ref {
        mutable: true,
        inner: Box::new(Ty::uint(32)),
    };
    let y = t1.param("y", y_ty, false);
    let x = t1.let_local("x", Ty::sint(32), true);
    let one = t1.lit(1, Ty::sint(32));
    let let_x = t1.stmt(StmtKind::Let {
        local: x,
        init: Some(one),
    });
    let (rx, two) = (t1.rd(x), t1.lit(2, Ty::sint(32)));
    let sum = t1.checked(BinOp::Add, rx, two);
    let add_assign = t1.assign(Place::local(x), sum);
    let (rx, three) = (t1.rd(x), t1.lit(3, Ty::sint(32)));
    let eq = t1.cmp(BinOp::Eq, rx, three);
    let assert_x = t1.assert(eq);
    let span = t1.span();
    let cur_y = Expr::read(Place::deref(y), Ty::uint(32), span);
    let two_u32 = t1.lit(2, Ty::uint(32));
    let quotient = t1.checked(BinOp::Div, cur_y, two_u32);
    let div_assign = t1.assign(Place::deref(y), quotient);
    let span = t1.span();
    let now = Expr::read(Place::deref(y), Ty::uint(32), span);
    let now = t1.int_of(now);
    let span = t1.span();
    let before = Expr::new(Ty::uint(32), span, ExprKind::Old(Place::deref(y)));
    let before = t1.int_of(before);
    let two_int = t1.lit(2, Ty::int());
    let half = t1.bin(BinOp::Div, before, two_int, Ty::int());
    let eq = t1.cmp(BinOp::Eq, now, half);
    let assert_y = t1.assert(eq);
    let ret = t1.ret(None);
    let t1 = t1.body(vec![let_x, add_assign, assert_x, div_assign, assert_y, ret]);

    let mut t2 = Fb::new(31, "test2a", Mode::Proof, Ty::Unit);
    let x = t2.let_local("x", Ty::uint(8), true);
    let init = t2.lit(200, Ty::uint(8));
    let let_x = t2.stmt(StmtKind::Let {
        local: x,
        init: Some(init),
    });
    let rx = t2.rd(x);
    let rx = t2.int_of(rx);
    let hundred = t2.lit(100, Ty::int());
    let sum = t2.bin(BinOp::Add, rx, hundred, Ty::int());
    let span = t2.span();
    let clipped = sum.cast(CastKind::As, Ty::uint(8), span);
    let assign = t2.assign(Place::local(x), clipped);
    let rx = t2.rd(x);
    let rx = t2.int_of(rx);
    let bound = t2.lit(256, Ty::int());
    let lt = t2.cmp(BinOp::Lt, rx, bound);
    let assert = t2.assert(lt);
    let ret = t2.ret(None);
    let t2 = t2.body(vec![let_x, assign, assert, ret]);
    krate(vec![t1, t2])
}

#[test]
fn compound_assign_is_well_formed() {
    assert_well_formed(&compound_assign_crate());
}

/// `struct Foo { b: bool }`, `spec fn get_b(foo: Foo) -> bool { foo.b }` and
/// `fn test1() -> (b: Foo) ensures get_b(b) { Foo { b: true } }`.
#[test]
fn struct_constructor_and_field_are_well_formed() {
    let foo = AdtId(DefHash::new(1, 1));
    let adt = AdtDecl {
        id: foo,
        name: "Foo".to_string(),
        type_params: Vec::new(),
        span: SpanId(1),
        kind: AdtKind::Struct,
        variants: vec![VariantDecl {
            name: "Foo".to_string(),
            fields: vec![FieldDecl {
                name: "b".to_string(),
                ty: Ty::Bool,
            }],
        }],
    };
    let mut get_b = Fb::new(40, "get_b", Mode::Spec, Ty::Bool);
    let param = get_b.param("foo", Ty::Adt(foo, Vec::new()), false);
    let base = get_b.rd(param);
    let span = get_b.span();
    let field = Expr::new(
        Ty::Bool,
        span,
        ExprKind::Field {
            base: Box::new(base),
            variant: 0,
            field: 0,
        },
    );
    let get_b = get_b.spec_body(field);

    let mut t = Fb::new(41, "test1", Mode::Exec, Ty::Adt(foo, Vec::new()));
    let ret_local = t.decl.ret;
    let rb = t.rd(ret_local);
    let ens = t.call(fn_id(40), vec![rb], Ty::Bool);
    let clause = t.clause(ens);
    t.decl.ensures = vec![clause];
    let tt = t.bool_lit(true);
    let span = t.span();
    let value = Expr::new(
        Ty::Adt(foo, Vec::new()),
        span,
        ExprKind::Ctor {
            adt: foo,
            variant: 0,
            fields: vec![tt],
        },
    );
    let ret = t.ret(Some(value));
    let t = t.body(vec![ret]);

    let mut krate = krate(vec![get_b, t]);
    krate.adts = vec![adt];
    assert_well_formed(&krate);
}

// ----------------------------------------------------------------------
// User errors (Verus's messages)
// ----------------------------------------------------------------------

#[test]
fn assigning_an_immutable_parameter() {
    // proof fn test1(x: u64) { x = 5; }
    let mut t = Fb::new(50, "test1", Mode::Proof, Ty::Unit);
    let x = t.param("x", Ty::uint(64), false);
    let five = t.lit(5, Ty::uint(64));
    let assign = t.assign(Place::local(x), five);
    let ret = t.ret(None);
    let errors = check_crate(&krate(vec![t.body(vec![assign, ret])]));
    assert_user_error(&errors, &msg_not_mutable("x"));

    // Twin: the same with `mut x` is fine.
    let mut t = Fb::new(50, "test1", Mode::Proof, Ty::Unit);
    let x = t.param("x", Ty::uint(64), true);
    let five = t.lit(5, Ty::uint(64));
    let assign = t.assign(Place::local(x), five);
    let ret = t.ret(None);
    assert_well_formed(&krate(vec![t.body(vec![assign, ret])]));
}

#[test]
fn assignment_in_a_spec_function() {
    // spec fn test1(x: u64) { x = 5; }
    let mut t = Fb::new(51, "test1", Mode::Spec, Ty::Unit);
    let x = t.param("x", Ty::uint(64), false);
    let five = t.lit(5, Ty::uint(64));
    let assign = t.assign(Place::local(x), five);
    let errors = check_crate(&krate(vec![t.body(vec![assign])]));
    assert_user_error(&errors, MSG_ASSIGN_IN_PURE);
}

#[test]
fn mut_parameter_of_a_spec_function() {
    // spec fn f(mut x: i32) -> i32;
    let mut t = Fb::new(52, "f", Mode::Spec, Ty::sint(32));
    t.param("x", Ty::sint(32), true);
    let errors = check_crate(&krate(vec![t.decl]));
    assert_user_error(&errors, MSG_MUT_SPEC_PARAM);
}

#[test]
fn duplicate_custom_err_on_an_assert() {
    let mut t = Fb::new(53, "caller", Mode::Exec, Ty::Unit);
    let (one, two) = (t.lit(1, Ty::int()), t.lit(2, Ty::int()));
    let gt = t.cmp(BinOp::Gt, one, two);
    let mut assert = t.assert(gt);
    if let StmtKind::Assert { attrs, .. } = &mut assert.kind {
        attrs.custom_errs = vec!["Custom assert error".to_string(), "Another".to_string()];
    }
    let ret = t.ret(None);
    let errors = check_crate(&krate(vec![t.body(vec![assert, ret])]));
    assert_user_error(&errors, MSG_DUPLICATE_NOTE);
}

#[test]
fn proof_call_from_exec_needs_a_ghost_block() {
    let mut lemma = Fb::new(60, "lemma", Mode::Proof, Ty::Unit);
    let ret = lemma.ret(None);
    let lemma = lemma.body(vec![ret]);

    let mut outside = Fb::new(61, "outside", Mode::Exec, Ty::Unit);
    let call = outside.call_stmt(fn_id(60), vec![], None);
    let ret = outside.ret(None);
    let outside = outside.body(vec![call, ret]);
    let errors = check_crate(&krate(vec![lemma.clone(), outside]));
    assert_user_error(&errors, MSG_CALL_PROOF_FROM_EXEC);

    let mut inside = Fb::new(61, "inside", Mode::Exec, Ty::Unit);
    let call = inside.call_stmt(fn_id(60), vec![], None);
    let ghost = inside.stmt(StmtKind::Ghost(Block::new(vec![call])));
    let ret = inside.ret(None);
    let inside = inside.body(vec![ghost, ret]);
    assert_well_formed(&krate(vec![lemma, inside]));
}

// ----------------------------------------------------------------------
// Malformed IR: producer mistakes the checker must catch
// ----------------------------------------------------------------------

#[test]
fn exec_check_inside_an_assertion_is_malformed() {
    let mut t = Fb::new(70, "t", Mode::Exec, Ty::Unit);
    let x = t.param("x", Ty::uint(8), false);
    let (rx, one) = (t.rd(x), t.lit(1, Ty::uint(8)));
    let sum = t.checked(BinOp::Add, rx, one);
    let zero = t.lit(0, Ty::uint(8));
    let gt = t.cmp(BinOp::Gt, sum, zero);
    let assert = t.assert(gt);
    let ret = t.ret(None);
    let errors = check_crate(&krate(vec![t.body(vec![assert, ret])]));
    assert_malformed(&errors, "exec check outside exec code");
}

#[test]
fn spec_arithmetic_on_machine_integers_is_malformed() {
    let mut t = Fb::new(71, "t", Mode::Spec, Ty::int());
    let x = t.param("x", Ty::uint(64), false);
    let (rx, one) = (t.rd(x), t.lit(1, Ty::uint(64)));
    let sum = t.bin(BinOp::Add, rx, one, Ty::int());
    let errors = check_crate(&krate(vec![t.spec_body(sum)]));
    assert_malformed(&errors, "cast the operands to int first");
}

#[test]
fn exact_cast_that_can_lose_information_is_malformed() {
    let mut t = Fb::new(72, "t", Mode::Spec, Ty::uint(8));
    let x = t.param("x", Ty::int(), false);
    let rx = t.rd(x);
    let span = t.span();
    let narrowed = rx.cast(CastKind::Exact, Ty::uint(8), span);
    let errors = check_crate(&krate(vec![t.spec_body(narrowed)]));
    assert_malformed(&errors, "exact cast");
}

#[test]
fn literal_out_of_range_is_malformed() {
    let mut t = Fb::new(73, "t", Mode::Spec, Ty::uint(8));
    let big = t.lit(256, Ty::uint(8));
    let errors = check_crate(&krate(vec![t.spec_body(big)]));
    assert_malformed(&errors, "does not fit");

    let mut t = Fb::new(73, "t", Mode::Spec, Ty::sint(8));
    let small = t.lit(-129, Ty::sint(8));
    let errors = check_crate(&krate(vec![t.spec_body(small)]));
    assert_malformed(&errors, "does not fit");

    let mut t = Fb::new(73, "t", Mode::Spec, Ty::sint(8));
    let edge = t.lit(-128, Ty::sint(8));
    assert_well_formed(&krate(vec![t.spec_body(edge)]));
}

#[test]
fn comparison_of_different_types_is_malformed() {
    let mut t = Fb::new(74, "t", Mode::Spec, Ty::Bool);
    let x = t.param("x", Ty::uint(64), false);
    let (rx, zero) = (t.rd(x), t.lit(0, Ty::int()));
    let eq = t.cmp(BinOp::Eq, rx, zero);
    let errors = check_crate(&krate(vec![t.spec_body(eq)]));
    assert_malformed(&errors, "different types");
}

#[test]
fn reused_site_is_malformed() {
    let mut t = Fb::new(75, "t", Mode::Exec, Ty::Unit);
    let tt = t.bool_lit(true);
    let first = t.stmt(StmtKind::Assert {
        expr: tt.clone(),
        site: SiteId(7),
        attrs: ClauseAttrs::default(),
    });
    let second = t.stmt(StmtKind::Assert {
        expr: tt,
        site: SiteId(7),
        attrs: ClauseAttrs::default(),
    });
    let ret = t.ret(None);
    let errors = check_crate(&krate(vec![t.body(vec![first, second, ret])]));
    assert_malformed(&errors, "used twice");
}

#[test]
fn precondition_reading_the_result_is_malformed() {
    let mut t = Fb::new(76, "t", Mode::Exec, Ty::uint(8));
    let ret_local = t.decl.ret;
    let (r, zero) = (t.rd(ret_local), t.lit(0, Ty::uint(8)));
    let gt = t.cmp(BinOp::Gt, r, zero);
    let clause = t.clause(gt);
    t.decl.requires = vec![clause];
    let one = t.lit(1, Ty::uint(8));
    let ret = t.ret(Some(one));
    let errors = check_crate(&krate(vec![t.body(vec![ret])]));
    assert_malformed(&errors, "precondition reads the return value");
}

#[test]
fn assignment_through_a_shared_reference_is_malformed() {
    let mut t = Fb::new(77, "t", Mode::Exec, Ty::Unit);
    let y = t.param(
        "y",
        Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::uint(32)),
        },
        false,
    );
    let zero = t.lit(0, Ty::uint(32));
    let assign = t.assign(Place::deref(y), zero);
    let ret = t.ret(None);
    let errors = check_crate(&krate(vec![t.body(vec![assign, ret])]));
    assert_malformed(&errors, "shared reference");
}

#[test]
fn returning_the_wrong_type_is_malformed() {
    let mut t = Fb::new(78, "t", Mode::Exec, Ty::uint(64));
    let five = t.lit(5, Ty::uint(32));
    let ret = t.ret(Some(five));
    let errors = check_crate(&krate(vec![t.body(vec![ret])]));
    assert_malformed(&errors, "returned value has the wrong type");
}

// ----------------------------------------------------------------------
// Integer ranges and literals
// ----------------------------------------------------------------------

#[test]
fn integer_bounds() {
    assert_eq!(IntRange::U(8).max(64), Some(255));
    assert_eq!(IntRange::U(8).min(64), Some(0));
    assert_eq!(IntRange::I(8).min(64), Some(-128));
    assert_eq!(IntRange::I(8).max(64), Some(127));
    assert_eq!(IntRange::I(128).min(64), Some(i128::MIN));
    assert_eq!(IntRange::I(128).max(64), Some(i128::MAX as u128));
    assert_eq!(IntRange::U(128).max(64), Some(u128::MAX));
    assert_eq!(IntRange::USize.max(32), Some(u128::from(u32::MAX)));
    assert_eq!(IntRange::Int.min(64), None);
    assert_eq!(IntRange::Nat.min(64), Some(0));
    assert_eq!(IntRange::Nat.max(64), None);
    assert!(IntRange::Int.contains(IntRange::Nat, 64));
    assert!(IntRange::Int.contains(IntRange::U(128), 64));
    assert!(IntRange::U(64).contains(IntRange::U(32), 64));
    assert!(IntRange::I(64).contains(IntRange::U(32), 64));
    assert!(!IntRange::I(32).contains(IntRange::U(32), 64));
    assert!(!IntRange::U(64).contains(IntRange::I(8), 64));
    assert!(!IntRange::Nat.contains(IntRange::Int, 64));
    assert!(IntRange::U(64).contains(IntRange::USize, 64));
    assert!(!IntRange::U(32).contains(IntRange::USize, 64));
    assert!(!IntRange::U(7).is_valid());
    // An invalid width must not panic.
    let _ = IntRange::U(0).max(64);
    let _ = IntRange::I(200).min(64);
}

#[test]
fn integer_literals_are_exact() {
    assert_eq!(IntLit::from_i128(i128::MIN).to_i128(), Some(i128::MIN));
    assert_eq!(IntLit::from_i128(-5).to_i128(), Some(-5));
    assert!(!IntLit::from_i128(0).negative);
    let max = IntLit {
        negative: false,
        magnitude: u128::MAX,
    };
    assert_eq!(max.to_i128(), None);
}

#[test]
fn constant_kind_cannot_turn_an_executable_initializer_into_a_spec_definition() {
    use trust_vc_vcir::{ConstMode, FnKind};
    let mut f = Fb::new(900, "value", Mode::Spec, Ty::int());
    let value = f.lit(7, Ty::int());
    let mut decl = f.spec_body(value);
    decl.kind = FnKind::Constant(ConstMode::Spec);
    assert!(check_crate(&krate(vec![decl.clone()])).is_empty());
    for kind in [
        FnKind::Constant(ConstMode::Dual),
        FnKind::Constant(ConstMode::Exec),
        FnKind::Static,
    ] {
        decl.kind = kind;
        let errors = check_crate(&krate(vec![decl.clone()]));
        assert!(
            errors.iter().any(|error| error.class == WfClass::Malformed),
            "{kind:?}: {errors:?}"
        );
    }
}

#[test]
fn spec_constant_declaration_and_return_modes_must_agree() {
    use trust_vc_vcir::{ConstMode, FnKind};
    let mut f = Fb::new(901, "value", Mode::Spec, Ty::int());
    let value = f.lit(7, Ty::int());
    let mut decl = f.spec_body(value);
    decl.kind = FnKind::Constant(ConstMode::Spec);
    decl.locals[decl.ret.index()].mode = Mode::Exec;
    let errors = check_crate(&krate(vec![decl]));
    assert!(
        errors.iter().any(|error| error.class == WfClass::Malformed
            && error.message.contains("spec declaration and return modes")),
        "{errors:?}"
    );
}
