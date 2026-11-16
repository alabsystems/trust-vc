use trust_vc_vcir::vcgen::{self, FnVcs};
use trust_vc_vcir::wf::ghost_tail_modes;
use trust_vc_vcir::*;

pub(super) fn id(n: u64) -> FnId {
    FnId(DefHash::new(151, n))
}
pub(super) fn sp(n: u32) -> SpanId {
    SpanId(n)
}
pub(super) fn local(ty: Ty, mode: Mode, kind: LocalKind) -> LocalDecl {
    LocalDecl {
        name: "value".into(),
        ty,
        mode,
        kind,
        prophecy: DeclProphecy::Default,
        mutable: kind == LocalKind::Temp,
        span: sp(0),
    }
}
pub(super) fn function(n: u64, mode: Mode, ty: Ty, result_mode: Mode) -> FnDecl {
    FnDecl {
        id: id(n),
        name: format!("function{n}"),
        span: sp(0),
        mode,
        role: FnRole::Item,
        kind: FnKind::Function,
        type_params: vec![],
        locals: vec![local(ty, result_mode, LocalKind::Return)],
        params: vec![],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        unwind: None,
        attrs: FnAttrs::default(),
        body: Body::None,
    }
}
pub(super) fn unit() -> Expr {
    Expr::new(Ty::Unit, sp(0), ExprKind::Lit(Lit::Unit))
}
pub(super) fn call(n: u64, ty: Ty) -> Expr {
    Expr::new(
        ty,
        sp(0),
        ExprKind::Call {
            callee: id(n),
            type_args: vec![],
            args: vec![],
        },
    )
}
pub(super) fn prophetic() -> Expr {
    call(1, Ty::Bool)
}
pub(super) fn read(local: LocalId) -> Expr {
    Expr::read(Place::local(local), Ty::Unit, sp(0))
}
pub(super) fn stmt(kind: StmtKind) -> Stmt {
    Stmt::new(sp(10), kind)
}
pub(super) fn end() -> Stmt {
    stmt(StmtKind::Return {
        value: None,
        site: SiteId(99),
    })
}
pub(super) fn source(mut client: FnDecl) -> VcCrate {
    let mut p = function(1, Mode::Spec, Ty::Bool, Mode::Spec);
    p.attrs.prophetic = true;
    p.body = Body::Spec(Expr::bool_lit(true, sp(0)));
    let mut implicit = function(2, Mode::Proof, Ty::Unit, Mode::Proof);
    implicit
        .locals
        .push(local(Ty::Bool, Mode::Spec, LocalKind::Param));
    implicit.params.push(LocalId(1));
    implicit.body = Body::Stmts(Block::new(vec![end()]));
    let mut written = implicit.clone();
    written.id = id(3);
    written.name = "written_spec_unit".into();
    written.locals[0].mode = Mode::Spec;
    let mut spec_unit = function(4, Mode::Spec, Ty::Unit, Mode::Spec);
    spec_unit.attrs.prophetic = true;
    spec_unit.body = Body::Spec(unit());
    if let Body::Stmts(block) = &mut client.body {
        block.stmts.push(end());
    }
    let mut k = VcCrate::new("raw proof tail modes");
    k.fns = vec![p, implicit, written, spec_unit, client];
    k
}
pub(super) fn client() -> FnDecl {
    let mut f = function(5, Mode::Exec, Ty::Unit, Mode::Exec);
    f.body = Body::Stmts(Block::default());
    f
}
pub(super) fn add_temp(f: &mut FnDecl) -> LocalId {
    let local_id = LocalId(f.locals.len() as u32);
    let mut decl = local(Ty::Unit, Mode::Spec, LocalKind::Temp);
    decl.prophecy = DeclProphecy::DelayedInfer;
    f.locals.push(decl);
    local_id
}
pub(super) fn invoke(n: u64, dest: Option<LocalId>, site: u32) -> Stmt {
    stmt(StmtKind::Call {
        callee: id(n),
        type_args: vec![],
        args: vec![prophetic()],
        dest: dest.map(Place::local),
        site: SiteId(site),
    })
}
pub(super) fn declaration(local: LocalId, init: Option<Expr>) -> Stmt {
    stmt(StmtKind::Let { local, init })
}
pub(super) fn tail(f: &mut FnDecl, prefix: Vec<Stmt>, value: Expr) {
    let Body::Stmts(body) = &mut f.body else {
        panic!()
    };
    body.stmts.push(Stmt::new(
        sp(20),
        StmtKind::GhostTail {
            block: Block::new(prefix),
            tail: value,
        },
    ));
}
pub(super) fn call_tail(callee: u64) -> VcCrate {
    let mut f = client();
    let result = add_temp(&mut f);
    tail(
        &mut f,
        vec![declaration(result, None), invoke(callee, Some(result), 0)],
        read(result),
    );
    source(f)
}
pub(super) fn accepted(k: &VcCrate) {
    assert!(check_crate(k).is_empty(), "{:?}", check_crate(k));
}
pub(super) fn rejects_wrap(k: &VcCrate) {
    let errors = check_crate(k);
    assert!(
        errors.iter().any(|error| error.function == Some(id(5))
            && error.class == WfClass::User
            && error.message.contains("'Ghost' wrapper")),
        "{errors:?}"
    );
    assert!(matches!(
        vcgen::generate(k).get(id(5)),
        Some(FnVcs::Refused(_))
    ));
}
pub(super) fn malformed(k: &VcCrate) {
    assert!(
        check_crate(k)
            .iter()
            .any(|error| error.function == Some(id(5))
                && error.class == WfClass::Malformed
                && error.message.contains("raw Unit value-mode origin")),
        "{:?}",
        check_crate(k)
    );
    assert_eq!(ghost_tail_modes(k).last().unwrap().class, None);
}
