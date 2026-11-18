//! Check placement is independent of Spec storage and value mode.
use super::*;

fn candidate(owner: Mode, storage: Mode, kind: LocalKind, ordinary: bool, ghost: bool) -> VcCrate {
    let mut f = Fb::new(1200, "checked_init", owner, Ty::Unit);
    let x = f.param("x", Ty::uint(8), false);
    f.decl.locals[x.index()].mode = Mode::Spec;
    let y = f.add_local("y", Ty::uint(8), storage, false, kind);
    if kind == LocalKind::Param {
        f.decl.params.push(y);
    }
    let left = f.rd(x);
    let right = f.lit(1, Ty::uint(8));
    let init = f.checked(BinOp::Add, left, right);
    let statement = f.stmt(if ordinary {
        StmtKind::Let {
            local: y,
            init: Some(init),
        }
    } else {
        StmtKind::LetChecked { local: y, init }
    });
    let body = if ghost {
        vec![f.stmt(StmtKind::Ghost(Block::new(vec![statement])))]
    } else {
        vec![statement]
    };
    krate(vec![f.body(body)])
}

#[test]
fn checked_spec_value_is_valid_without_promoting_storage_or_markers() {
    for kind in [LocalKind::Let, LocalKind::Temp] {
        for marker in [
            trust_vc_vcir::DeclProphecy::Default,
            trust_vc_vcir::DeclProphecy::Prophetic,
            trust_vc_vcir::DeclProphecy::DelayedInfer,
        ] {
            let mut k = candidate(Mode::Exec, Mode::Spec, kind, false, false);
            k.fns[0].locals[2].prophecy = marker;
            assert!(check_crate(&k).is_empty(), "{:?}", check_crate(&k));
            assert_eq!(k.fns[0].locals[2].mode, Mode::Spec);
            assert_eq!(k.fns[0].locals[2].prophecy, marker);
        }
    }
}

#[test]
fn ordinary_spec_let_still_cannot_carry_exec_checks() {
    let k = candidate(Mode::Exec, Mode::Spec, LocalKind::Let, true, false);
    assert_malformed(&check_crate(&k), "exec check outside exec code");
}

#[test]
fn checked_evaluation_with_no_sites_does_not_grant_a_new_value_mode() {
    let mut k = candidate(Mode::Exec, Mode::Spec, LocalKind::Let, false, false);
    let Body::Stmts(block) = &mut k.fns[0].body else {
        unreachable!()
    };
    let StmtKind::LetChecked { init, .. } = &mut block.stmts[0].kind else {
        unreachable!()
    };
    *init = Expr::read(Place::local(LocalId(1)), Ty::uint(8), SpanId(40));
    assert!(check_crate(&k).is_empty(), "{:?}", check_crate(&k));
    assert_eq!(k.fns[0].locals[2].mode, Mode::Spec);
}

#[test]
fn checked_let_rejects_proof_context_and_non_spec_storage() {
    for k in [
        candidate(Mode::Proof, Mode::Spec, LocalKind::Let, false, false),
        candidate(Mode::Exec, Mode::Spec, LocalKind::Let, false, true),
        candidate(Mode::Exec, Mode::Exec, LocalKind::Let, false, false),
        candidate(Mode::Exec, Mode::Proof, LocalKind::Let, false, false),
    ] {
        assert_malformed(
            &check_crate(&k),
            "checked initializer requires Exec context and Spec storage",
        );
    }
}

#[test]
fn checked_let_cannot_initialize_a_parameter_return_or_bound_local() {
    for kind in [LocalKind::Param, LocalKind::Return, LocalKind::Bound] {
        let k = candidate(Mode::Exec, Mode::Spec, kind, false, false);
        assert_malformed(&check_crate(&k), "not a let local");
    }
}

#[test]
fn checked_let_retains_exact_types_and_unique_check_sites() {
    let mut mismatch = candidate(Mode::Exec, Mode::Spec, LocalKind::Let, false, false);
    mismatch.fns[0].locals[2].ty = Ty::Bool;
    assert_malformed(&check_crate(&mismatch), "wrong type");
    let mut duplicate = candidate(Mode::Exec, Mode::Spec, LocalKind::Let, false, false);
    let Body::Stmts(block) = &mut duplicate.fns[0].body else {
        unreachable!()
    };
    block.stmts.push(block.stmts[0].clone());
    assert_malformed(&check_crate(&duplicate), "site");
}
