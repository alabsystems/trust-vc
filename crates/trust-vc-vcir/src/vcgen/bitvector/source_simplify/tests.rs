use super::super::super::val::{Ctx, Val};
use super::super::*;
use crate::{AdtDecl, AdtId, AdtKind, DefHash, SpanId, VariantDecl, VcCrate};

fn equality(left: Expr, right: Expr) -> Expr {
    Expr::binary(BinOp::Eq, left, right, Ty::Bool, SpanId(3))
}

fn input(ty: Ty) -> Expr {
    Expr::read(Place::local(LocalId(1)), ty, SpanId(1))
}

fn admitted(
    krate: &VcCrate,
    goal: &Expr,
    available: bool,
    policy: super::super::super::BitvectorPolicy,
) -> R<Query> {
    let mut ctx = Ctx::new(krate);
    ctx.bitvector_policy = policy;
    let mut reads = Reads::default();
    if available {
        let value = if krate.adts.is_empty() {
            Val::Leaf(super::super::super::term::Term::Int(0))
        } else {
            Val::Node(vec![])
        };
        reads.read.insert(LocalId(1), value);
    }
    super::super::lower(&ctx, &[], goal, &reads, 64)
}

#[test]
fn source_policy_folds_equal_math_inputs_without_granting_rich_ir_an_input() {
    let krate = VcCrate::new("typed BV source preprocessing");
    let left = input(Ty::int());
    let mut right = left.clone();
    right.span = SpanId(2);
    let goal = equality(left, right);
    let default = super::super::super::BitvectorPolicy::PreserveOperations;
    let source = super::super::super::BitvectorPolicy::VerusSyntactic;
    assert!(admitted(&krate, &goal, true, default).is_err());
    let query = admitted(&krate, &goal, true, source).unwrap();
    assert!(query.variables.is_empty());
    assert_eq!(query.goal, Term::Bool(true));
}

#[test]
fn an_identity_cannot_manufacture_source_availability() {
    let krate = VcCrate::new("typed BV source availability");
    let value = input(Ty::uint(32));
    let goal = equality(value.clone(), value);
    let error = admitted(
        &krate,
        &goal,
        false,
        super::super::super::BitvectorPolicy::VerusSyntactic,
    )
    .unwrap_err();
    assert_eq!(error.tag, "bit-vector-expression");
    assert!(error.detail.contains("unavailable or uninitialized"));
}

#[test]
fn zero_division_occurrences_are_only_identified_by_explicit_source_policy() {
    let krate = VcCrate::new("typed BV zero operation preprocessing");
    for op in [BinOp::Div, BinOp::Rem] {
        let ty = Ty::uint(8);
        let operation = Expr::binary(
            op,
            input(ty.clone()),
            Expr::int_lit(0, ty.clone(), SpanId(1)),
            ty,
            SpanId(1),
        );
        let goal = equality(operation.clone(), operation);
        let raw = admitted(
            &krate,
            &goal,
            true,
            super::super::super::BitvectorPolicy::PreserveOperations,
        )
        .unwrap();
        let projected = admitted(
            &krate,
            &goal,
            true,
            super::super::super::BitvectorPolicy::VerusSyntactic,
        )
        .unwrap();
        assert_ne!(raw.goal, Term::Bool(true));
        assert_eq!(projected.goal, Term::Bool(true));
        assert!(projected.variables.is_empty());
    }
}

#[test]
fn product_identity_is_removed_before_product_value_conversion() {
    let id = AdtId(DefHash::new(93, 1));
    let mut krate = VcCrate::new("typed BV product preprocessing");
    krate.adts.push(AdtDecl {
        id,
        name: "test_crate::X".into(),
        type_params: vec![],
        span: SpanId(0),
        kind: AdtKind::Struct,
        variants: vec![VariantDecl {
            name: "X".into(),
            fields: vec![],
        }],
    });
    let value = input(Ty::Adt(id, vec![]));
    let goal = equality(value.clone(), value);
    let projected = admitted(
        &krate,
        &goal,
        true,
        super::super::super::BitvectorPolicy::VerusSyntactic,
    )
    .unwrap();
    assert_eq!(projected.goal, Term::Bool(true));
}

#[test]
fn checked_operations_and_changed_places_keep_their_original_lowering() {
    let krate = VcCrate::new("typed BV source validity");
    let ty = Ty::uint(8);
    let checked = Expr::checked_binary(
        BinOp::Add,
        input(ty.clone()),
        Expr::int_lit(1, ty.clone(), SpanId(1)),
        ty.clone(),
        crate::SiteId(4),
        SpanId(1),
    );
    let goal = equality(checked.clone(), checked);
    let error = admitted(
        &krate,
        &goal,
        true,
        super::super::super::BitvectorPolicy::VerusSyntactic,
    )
    .unwrap_err();
    assert!(error.detail.contains("checked binary"));

    let goal = equality(
        input(ty.clone()),
        Expr::read(Place::local(LocalId(2)), ty, SpanId(2)),
    );
    let error = admitted(
        &krate,
        &goal,
        true,
        super::super::super::BitvectorPolicy::VerusSyntactic,
    )
    .unwrap_err();
    assert!(error.detail.contains("unavailable or uninitialized"));
}

#[test]
fn full_syntax_admission_uses_the_same_projection_without_creating_a_value() {
    let krate = VcCrate::new("typed BV admission preprocessing");
    let value = input(Ty::int());
    let goal = equality(value.clone(), value);
    let mut ctx = Ctx::new(&krate);
    ctx.bitvector_policy = super::super::super::BitvectorPolicy::VerusSyntactic;
    let mut work = 200_000;
    super::super::admit_syntax(&ctx, &goal, &mut work).unwrap();
    assert!(work < 200_000);
    ctx.bitvector_policy = super::super::super::BitvectorPolicy::PreserveOperations;
    assert!(super::super::admit_syntax(&ctx, &goal, &mut work).is_err());
}
