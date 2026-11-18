//! Physical checked evaluation does not authorize logical Exec effects.
use super::*;

fn conditional(f: &mut Fb, cond: Expr, body: Vec<Stmt>) -> Stmt {
    f.stmt(StmtKind::IfSpec {
        cond,
        then_block: Block::new(body),
        else_block: Block::default(),
    })
}

fn checked_assignment(owner: Mode, target: Mode, ghost: bool) -> VcCrate {
    let mut f = Fb::new(1500, "checked_assignment", owner, Ty::Unit);
    let x = f.param("x", Ty::uint(8), false);
    f.decl.locals[x.index()].mode = Mode::Spec;
    let y = f.add_local("y", Ty::uint(8), target, true, LocalKind::Let);
    let zero = f.lit(0, Ty::uint(8));
    let declared = f.stmt(StmtKind::Let {
        local: y,
        init: Some(zero),
    });
    let x = f.rd(x);
    let one = f.lit(1, Ty::uint(8));
    let value = f.checked(BinOp::Add, x, one);
    let assignment = f.stmt(StmtKind::AssignSpec {
        place: Place::local(y),
        value,
    });
    let assignment = if ghost {
        f.stmt(StmtKind::Ghost(Block::new(vec![assignment])))
    } else {
        assignment
    };
    krate(vec![f.body(vec![declared, assignment])])
}

#[test]
fn spec_condition_allows_checked_spec_arms_and_restores_exec_context() {
    let mut f = Fb::new(1501, "spec_condition", Mode::Exec, Ty::Unit);
    let condition = f.param("condition", Ty::Bool, false);
    f.decl.locals[condition.index()].mode = Mode::Spec;
    let x = f.param("x", Ty::uint(8), false);
    f.decl.locals[x.index()].mode = Mode::Spec;
    let y = f.add_local("y", Ty::uint(8), Mode::Spec, false, LocalKind::Let);
    let x = f.rd(x);
    let one = f.lit(1, Ty::uint(8));
    let init = f.checked(BinOp::Add, x, one);
    let checked = f.stmt(StmtKind::LetChecked { local: y, init });
    let c = f.rd(condition);
    let branch = conditional(&mut f, c, vec![checked]);
    let exec = f.let_local("exec", Ty::Bool, true);
    let value = f.bool_lit(false);
    let declared = f.stmt(StmtKind::Let {
        local: exec,
        init: Some(value),
    });
    let value = f.bool_lit(true);
    let assigned = f.assign(Place::local(exec), value);
    let returned = f.ret(None);
    let k = krate(vec![f.body(vec![branch, declared, assigned, returned])]);
    assert!(check_crate(&k).is_empty(), "{:?}", check_crate(&k));
    assert!(check_crate(&checked_assignment(Mode::Exec, Mode::Spec, false)).is_empty());
}

#[test]
fn ordinary_if_still_requires_exec_condition_and_ifspec_requires_physical_exec() {
    let mut f = Fb::new(1502, "ordinary", Mode::Exec, Ty::Unit);
    let c = f.param("c", Ty::Bool, false);
    f.decl.locals[c.index()].mode = Mode::Spec;
    let cond = f.rd(c);
    let branch = f.stmt(StmtKind::If {
        cond,
        then_block: Block::default(),
        else_block: Block::default(),
    });
    let errors = check_crate(&krate(vec![f.body(vec![branch])]));
    assert!(
        errors
            .iter()
            .any(|e| e.message.contains("expected mode exec")),
        "{errors:?}"
    );
    for (owner, ghost) in [(Mode::Proof, false), (Mode::Exec, true)] {
        let mut f = Fb::new(1503, "wrong_context", owner, Ty::Unit);
        let cond = f.bool_lit(true);
        let branch = conditional(&mut f, cond, vec![]);
        let branch = if ghost {
            f.stmt(StmtKind::Ghost(Block::new(vec![branch])))
        } else {
            branch
        };
        assert_malformed(
            &check_crate(&krate(vec![f.body(vec![branch])])),
            "outside physical Exec",
        );
    }
}

#[test]
fn spec_control_cannot_write_call_return_or_borrow_exec_effects() {
    for effect in 0..5 {
        let mut f = Fb::new(1510 + effect, "effect", Mode::Exec, Ty::Unit);
        let x = f.param("x", Ty::Bool, true);
        let r = f.add_local(
            "r",
            Ty::MutRef(Box::new(Ty::Bool)),
            Mode::Proof,
            false,
            LocalKind::Temp,
        );
        let declaration = f.stmt(StmtKind::Let {
            local: r,
            init: None,
        });
        let statement = match effect {
            0 => {
                let value = f.bool_lit(true);
                f.assign(Place::local(x), value)
            }
            1 => f.call_stmt(fn_id(1520), vec![], None),
            2 => f.ret(None),
            3 => {
                let returned = f.ret(None);
                f.stmt(StmtKind::Ghost(Block::new(vec![returned])))
            }
            _ => f.stmt(StmtKind::BorrowMut {
                dest: r,
                place: Place::local(x),
            }),
        };
        let cond = f.bool_lit(true);
        let branch = conditional(&mut f, cond, vec![statement]);
        let mut callee = Fb::new(1520, "exec_callee", Mode::Exec, Ty::Unit);
        let ret = callee.ret(None);
        let errors = check_crate(&krate(vec![
            f.body(vec![declaration, branch]),
            callee.body(vec![ret]),
        ]));
        let expected = match effect {
            0 => "cannot assign to exec variable",
            1 => "with mode exec",
            2 | 3 => "cannot return from exec function in spec-controlled code",
            _ => "cannot mutably borrow exec storage",
        };
        assert!(
            errors.iter().any(|e| e.message.contains(expected)),
            "{effect}: {errors:?}"
        );
    }
}

#[test]
fn checked_assignment_requires_exact_mutable_spec_storage_and_physical_exec() {
    for (owner, target, ghost, expected) in [
        (Mode::Exec, Mode::Exec, false, "requires Spec storage"),
        (Mode::Exec, Mode::Proof, false, "requires Spec storage"),
        (Mode::Proof, Mode::Spec, false, "outside physical Exec"),
        (Mode::Exec, Mode::Spec, true, "outside physical Exec"),
    ] {
        assert_malformed(
            &check_crate(&checked_assignment(owner, target, ghost)),
            expected,
        );
    }
    let mut immutable = checked_assignment(Mode::Exec, Mode::Spec, false);
    let target = LocalId(2);
    // Ordinary WF rejects an immutable parameter. Assignment counts for
    // immutable Let storage are a separate native ownership obligation.
    immutable.fns[0].locals[target.index()].mutable = false;
    immutable.fns[0].locals[target.index()].kind = LocalKind::Param;
    immutable.fns[0].params.push(target);
    let Body::Stmts(block) = &mut immutable.fns[0].body else {
        unreachable!()
    };
    assert!(matches!(block.stmts.remove(0).kind, StmtKind::Let { local, .. } if local == target));
    let errors = check_crate(&immutable);
    assert!(
        errors
            .iter()
            .any(|e| e.message.contains("not marked mutable")),
        "{errors:?}"
    );
    let mut wrong_type = checked_assignment(Mode::Exec, Mode::Spec, false);
    let Body::Stmts(block) = &mut wrong_type.fns[0].body else {
        unreachable!()
    };
    let StmtKind::AssignSpec { value, .. } = &mut block.stmts[1].kind else {
        unreachable!()
    };
    *value = Expr::bool_lit(true, SpanId(99));
    assert_malformed(
        &check_crate(&wrong_type),
        "assigned value has the wrong type",
    );
}

#[test]
fn spec_control_preserves_pointee_modes_and_explicit_ghost_check_boundaries() {
    let mut f = Fb::new(1521, "pointee_effect", Mode::Exec, Ty::Unit);
    let pointer = f.param("pointer", Ty::MutRef(Box::new(Ty::Bool)), false);
    f.decl.locals[pointer.index()].mode = Mode::Proof;
    let value = f.bool_lit(true);
    let assigned = f.assign(Place::deref(pointer), value);
    let cond = f.bool_lit(true);
    let branch = conditional(&mut f, cond, vec![assigned]);
    let errors = check_crate(&krate(vec![f.body(vec![branch])]));
    assert!(
        errors
            .iter()
            .any(|e| e.message.contains("cannot assign to exec variable")),
        "{errors:?}"
    );

    let mut f = Fb::new(1522, "ghost_check", Mode::Exec, Ty::Unit);
    let y = f.add_local("y", Ty::uint(8), Mode::Spec, false, LocalKind::Let);
    let a = f.lit(0, Ty::uint(8));
    let b = f.lit(1, Ty::uint(8));
    let init = f.checked(BinOp::Add, a, b);
    let declared = f.stmt(StmtKind::LetChecked { local: y, init });
    let ghost = f.stmt(StmtKind::Ghost(Block::new(vec![declared])));
    let cond = f.bool_lit(true);
    let branch = conditional(&mut f, cond, vec![ghost]);
    assert_malformed(
        &check_crate(&krate(vec![f.body(vec![branch])])),
        "checked initializer requires Exec context",
    );
}
